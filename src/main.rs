//! The kalyx command-line program.
//!
//! The program runs requests of the command entry: `eval`, `expand` and
//! `diff`. Given an operation in its arguments, it runs that one request
//! (argument mode); given no argument, it reads one request from each line
//! of its standard input (line mode). For every request it creates a fresh
//! context with the limits of the request and a cancellation flag of its
//! own, runs [`execute`], and writes the line of the outcome that
//! [`serialize`] gives, whole, to standard output. It writes results in no
//! other form. Diagnostics go to standard error, and the exit status says
//! how the run went.
//!
//! `README.md` shows how to run the program; the command-line forms, the
//! line format and the exit statuses are stated in `docs/semantics.md`.

use std::env::args_os;
use std::ffi::OsString;
use std::io::{BufRead, IsTerminal, Write, stderr, stdin, stdout};
use std::process::ExitCode;

use kalyx::command::serialize;
use kalyx::context::CancelFlag;
use kalyx::{Context, Limits, Outcome, Request, execute};

/// The exit status when every request gave a value or a state, or when the
/// version or the usage text was written as asked.
const SUCCESS: u8 = 0;

/// The exit status when some request ended with an error, or its value did
/// not fit the limits of the request.
const REQUEST_FAILED: u8 = 1;

/// The exit status of a usage error: arguments that the program does not
/// accept, or a line of line mode that is not a request.
const USAGE: u8 = 2;

/// The exit status when reading standard input or writing standard output
/// fails, as when the reader of a pipe has closed it.
const STREAM_FAILED: u8 = 3;

/// The number of the fields of `Limits`, which the limits of a request may
/// set.
const LIMIT_FIELDS: usize = 9;

/// The usage text, written for `--help` and after a usage error.
const USAGE_TEXT: &str = "\
Usage: kalyx [--limits LIMITS] OPERATION [VARIABLE] INPUT
       kalyx
       kalyx --version
       kalyx --help

With an operation, runs one request: eval INPUT, expand VARIABLE INPUT or
diff VARIABLE INPUT. Without arguments, reads one request from each line of
standard input: OPERATION, VARIABLE, INPUT and optionally LIMITS, separated
by tabs. LIMITS is - or field=value settings separated by ;, such as
max_work=1000;max_depth=32. Writes one result line per request to standard
output.

Exit status: 0 every request gave a value, 1 a request failed, 2 usage
error, 3 reading standard input or writing standard output failed.
";

/// What the arguments ask the program to do.
#[derive(Debug, PartialEq, Eq)]
enum Invocation {
    /// `--version`: write the name and the version of the package.
    Version,
    /// `--help`: write the usage text.
    Help,
    /// No argument: line mode.
    Lines,
    /// An operation: argument mode, one request under its limits.
    Single(Request, Limits),
}

/// How the line of one request went.
#[derive(Debug, PartialEq, Eq)]
enum Reply {
    /// The request gave a value or a state, and its line was written.
    Answered,
    /// The request ended with an error, and its error line was written.
    Failed,
    /// The request has no line: its value or state did not fit the limits
    /// of the request, so nothing was written.
    Unwritten,
    /// Writing the line failed.
    WriteFailed,
}

/// The result of reading one line of standard input.
#[derive(Debug, PartialEq, Eq)]
enum LineRead {
    /// A line was read, without its line feed.
    Line,
    /// The input has ended, and no byte of a further line was read.
    End,
    /// Reading failed.
    Failed,
}

fn main() -> ExitCode {
    let arguments: Vec<OsString> = args_os().skip(1).collect();
    ExitCode::from(run(arguments))
}

/// Runs the program on `arguments`, the arguments after the program name,
/// and returns its exit status.
fn run(arguments: Vec<OsString>) -> u8 {
    match invocation(arguments) {
        Ok(Invocation::Version) => write_text(&version_text()),
        Ok(Invocation::Help) => write_text(USAGE_TEXT),
        Ok(Invocation::Lines) => run_lines(),
        Ok(Invocation::Single(request, limits)) => run_single(&request, limits),
        Err(problem) => {
            let mut err = stderr().lock();
            // Nothing is left to report a failed write of standard error to.
            let _ = write!(err, "kalyx: {problem}\n\n{USAGE_TEXT}");
            let _ = err.flush();
            USAGE
        }
    }
}

/// The text of `--version`: the name and the version of the package.
fn version_text() -> String {
    let mut text = String::from("kalyx ");
    text.push_str(env!("CARGO_PKG_VERSION"));
    text.push('\n');
    text
}

/// Writes `text` to standard output and returns the exit status.
fn write_text(text: &str) -> u8 {
    let mut out = stdout().lock();
    if write_line(&mut out, text.as_bytes()) {
        SUCCESS
    } else {
        report("cannot write to standard output");
        STREAM_FAILED
    }
}

/// Reads the invocation from `arguments`.
///
/// # Errors
///
/// The usage problem, when an argument is not UTF-8, names an unknown
/// option, or gives `--limits` without a valid value or without an
/// operation, or an operation without an input or with more than two
/// operands.
fn invocation(arguments: Vec<OsString>) -> Result<Invocation, &'static str> {
    let mut texts = Vec::with_capacity(arguments.len());
    for argument in arguments {
        match argument.into_string() {
            Ok(text) => texts.push(text),
            Err(_) => return Err("an argument is not UTF-8"),
        }
    }
    match texts.as_slice() {
        [] => Ok(Invocation::Lines),
        [only] if only == "--version" => Ok(Invocation::Version),
        [only] if only == "--help" || only == "-h" => Ok(Invocation::Help),
        [only] if only == "--limits" => Err("--limits needs a value"),
        [option, spec, rest @ ..] if option == "--limits" => match limits_of(spec) {
            Ok(limits) => single(rest, limits),
            Err(problem) => Err(problem),
        },
        rest => single(rest, Limits::new()),
    }
}

/// The invocation of argument mode for `rest`, the operation and its
/// operands, under `limits`.
fn single(rest: &[String], limits: Limits) -> Result<Invocation, &'static str> {
    match rest {
        [] => Err("--limits needs an operation"),
        [operation, ..] if operation.starts_with('-') => Err("unknown option"),
        [_] => Err("the operation needs an input"),
        [operation, input] => Ok(Invocation::Single(
            Request::new(operation, "", input),
            limits,
        )),
        [operation, variable, input] => Ok(Invocation::Single(
            Request::new(operation, variable, input),
            limits,
        )),
        _ => Err("too many arguments: an operation takes a variable and an input"),
    }
}

/// Argument mode: runs `request` under `limits` and returns the exit status.
fn run_single(request: &Request, limits: Limits) -> u8 {
    let mut context = Context::new(limits, CancelFlag::new());
    let mut out = stdout().lock();
    let reply = respond(request, &mut context, &mut out);
    status_of(&reply, None)
}

/// Line mode: runs the request of every line of standard input, in order,
/// and returns the exit status, the highest of the statuses of its lines.
/// A failure to read or to write ends the run at once.
fn run_lines() -> u8 {
    let input = stdin();
    if input.is_terminal() {
        report(
            "reading requests from the terminal, one per line: \
             OPERATION<tab>VARIABLE<tab>INPUT[<tab>LIMITS]; end the input with Ctrl-D",
        );
    }
    let mut reader = input.lock();
    let mut out = stdout().lock();
    let mut line = Vec::new();
    let mut number: u64 = 0;
    let mut status = SUCCESS;
    loop {
        match read_line(&mut reader, &mut line) {
            LineRead::Line => {}
            LineRead::End => return status,
            LineRead::Failed => {
                report("cannot read standard input");
                return STREAM_FAILED;
            }
        }
        number = number.saturating_add(1);
        let line_status = run_line(&line, number, &mut out);
        if line_status == STREAM_FAILED {
            return STREAM_FAILED;
        }
        status = status.max(line_status);
    }
}

/// Runs the request of `line`, the line `number` of line mode, writes its
/// line to `out` and returns its exit status.
fn run_line<W: Write>(line: &[u8], number: u64, out: &mut W) -> u8 {
    match request_of_line(line) {
        Ok((request, limits)) => {
            let mut context = Context::new(limits, CancelFlag::new());
            let reply = respond(&request, &mut context, out);
            status_of(&reply, Some(number))
        }
        Err(problem) => {
            report_line(number, problem);
            USAGE
        }
    }
}

/// The exit status of `reply`, after its diagnostic, if it has one, on
/// standard error; `number` is the number of its line in line mode.
fn status_of(reply: &Reply, number: Option<u64>) -> u8 {
    match reply {
        Reply::Answered => SUCCESS,
        Reply::Failed => REQUEST_FAILED,
        Reply::Unwritten => {
            let problem = "the result does not fit the limits of its request, so it has no line";
            match number {
                Some(number) => report_line(number, problem),
                None => report(problem),
            }
            REQUEST_FAILED
        }
        Reply::WriteFailed => {
            report("cannot write to standard output");
            STREAM_FAILED
        }
    }
}

/// Runs `request` under `context` and writes the line of its outcome to
/// `out`, whole, with one `write!`, then flushes `out`.
///
/// The line is complete before any byte of it is written: the line under
/// `context`, or, when that fails and the outcome is an error, the line
/// under a fresh context with the default limits, a fresh flag and no
/// deadline, the fallback step of the contract of the command entry. A
/// value or a state whose line fails under `context` is never written, so a
/// cancellation or a limit leaves the whole line or nothing.
fn respond<W: Write>(request: &Request, context: &mut Context, out: &mut W) -> Reply {
    let outcome = execute(request, context);
    let Some(line) = line_of(&outcome, context) else {
        return Reply::Unwritten;
    };
    if !write_line(out, &line) {
        return Reply::WriteFailed;
    }
    match outcome.result() {
        Ok(_) => Reply::Answered,
        Err(_) => Reply::Failed,
    }
}

/// The line of `outcome`: under `context`, or under a fresh default context
/// when that fails and the outcome is an error; `None` otherwise.
fn line_of(outcome: &Outcome, context: &mut Context) -> Option<Vec<u8>> {
    match serialize(outcome, context) {
        Ok(line) => Some(line),
        Err(_) => fallback_line(outcome),
    }
}

/// The fallback step: the line of an error outcome under
/// `Context::new(Limits::new(), CancelFlag::new())`. A value or a state is
/// never written again.
fn fallback_line(outcome: &Outcome) -> Option<Vec<u8>> {
    match outcome.result() {
        Err(_) => {
            let mut fresh = Context::new(Limits::new(), CancelFlag::new());
            serialize(outcome, &mut fresh).ok()
        }
        Ok(_) => None,
    }
}

/// Writes `bytes`, one output line of UTF-8 text, to `out` with one
/// `write!` and flushes `out`; whether both succeeded.
fn write_line<W: Write>(out: &mut W, bytes: &[u8]) -> bool {
    let Ok(text) = std::str::from_utf8(bytes) else {
        return false;
    };
    if write!(out, "{text}").is_err() {
        return false;
    }
    out.flush().is_ok()
}

/// Writes `problem` to standard error as a diagnostic of the program.
fn report(problem: &str) {
    let mut err = stderr().lock();
    // Nothing is left to report a failed write of standard error to.
    let _ = writeln!(err, "kalyx: {problem}");
    let _ = err.flush();
}

/// Writes `problem` to standard error as a diagnostic of line `number`.
fn report_line(number: u64, problem: &str) {
    let mut err = stderr().lock();
    // Nothing is left to report a failed write of standard error to.
    let _ = writeln!(err, "kalyx: line {number}: {problem}");
    let _ = err.flush();
}

/// Reads the next line of `reader` into `line`, without its line feed,
/// with `fill_buf` and `consume`. A read of 0 bytes is the end of the
/// input, and the last line may lack its line feed.
fn read_line<R: BufRead>(reader: &mut R, line: &mut Vec<u8>) -> LineRead {
    line.clear();
    let mut started = false;
    loop {
        let (used, ended) = match reader.fill_buf() {
            Ok([]) if started => return LineRead::Line,
            Ok([]) => return LineRead::End,
            Ok(buffer) => take_line_bytes(buffer, line),
            Err(_) => return LineRead::Failed,
        };
        started = true;
        reader.consume(used);
        if ended {
            return LineRead::Line;
        }
    }
}

/// Appends the bytes of `buffer` before its first line feed to `line`;
/// returns the number of bytes used, the line feed included, and whether
/// the line ended.
fn take_line_bytes(buffer: &[u8], line: &mut Vec<u8>) -> (usize, bool) {
    let mut index = 0;
    while index < buffer.len() {
        if buffer[index] == b'\n' {
            line.extend_from_slice(&buffer[..index]);
            return (index + 1, true);
        }
        index += 1;
    }
    line.extend_from_slice(buffer);
    (buffer.len(), false)
}

/// The request and the limits of `bytes`, a line of line mode without its
/// line feed: up to four fields separated by tabs, the operation, the
/// variable, the input and the limits, of which the missing ones are empty;
/// one carriage return at the end of the line is dropped.
///
/// # Errors
///
/// The problem of a line that is not a request: it is not UTF-8, has more
/// than four fields, or its limits are not valid.
fn request_of_line(bytes: &[u8]) -> Result<(Request, Limits), &'static str> {
    let bytes = match bytes {
        [rest @ .., b'\r'] => rest,
        _ => bytes,
    };
    let Ok(text) = std::str::from_utf8(bytes) else {
        return Err("the line is not UTF-8");
    };
    match fields(text).as_slice() {
        [operation] => Ok((Request::new(operation, "", ""), Limits::new())),
        [operation, variable] => Ok((Request::new(operation, variable, ""), Limits::new())),
        [operation, variable, input] => {
            Ok((Request::new(operation, variable, input), Limits::new()))
        }
        [operation, variable, input, spec] => match limits_of(spec) {
            Ok(limits) => Ok((Request::new(operation, variable, input), limits)),
            Err(problem) => Err(problem),
        },
        _ => Err("the line has more than four fields"),
    }
}

/// The fields of `text`, separated by tabs.
fn fields(text: &str) -> Vec<&str> {
    let bytes = text.as_bytes();
    let mut fields = Vec::new();
    let mut start = 0;
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] == b'\t' {
            fields.push(&text[start..index]);
            start = index + 1;
        }
        index += 1;
    }
    fields.push(&text[start..]);
    fields
}

/// The limits that `spec` gives: the default limits for `-` or the empty
/// text, otherwise the defaults with the `field=value` settings of `spec`,
/// separated by `;`, applied, the format of the `limits` column of the
/// answer vectors.
///
/// # Errors
///
/// The problem of a setting without `=`, of an unknown field of `Limits`, of
/// a field set twice, or of a value that is not the decimal digits of a
/// `u64`.
fn limits_of(spec: &str) -> Result<Limits, &'static str> {
    if spec.is_empty() || spec == "-" {
        Ok(Limits::new())
    } else {
        apply_settings(spec)
    }
}

/// The default limits with the settings of `spec` applied.
fn apply_settings(spec: &str) -> Result<Limits, &'static str> {
    let bytes = spec.as_bytes();
    let mut limits = Limits::new();
    let mut seen = [false; LIMIT_FIELDS];
    let mut start = 0;
    let mut index = 0;
    while index <= bytes.len() {
        if index == bytes.len() || bytes[index] == b';' {
            let (changed, field) = apply_setting(limits, &spec[start..index])?;
            if seen[field] {
                return Err("a limit is set twice");
            }
            seen[field] = true;
            limits = changed;
            start = index + 1;
        }
        index += 1;
    }
    Ok(limits)
}

/// `limits` with the setting `field=value` applied, and the index of the
/// field.
fn apply_setting(limits: Limits, setting: &str) -> Result<(Limits, usize), &'static str> {
    let Some((name, digits)) = setting.split_once('=') else {
        return Err("a limit setting has no `=`");
    };
    let value = decimal(digits)?;
    match name {
        "max_work" => Ok((limits.with_max_work(value), 0)),
        "max_input_bytes" => Ok((limits.with_max_input_bytes(value), 1)),
        "max_output_bytes" => Ok((limits.with_max_output_bytes(value), 2)),
        "max_depth" => Ok((limits.with_max_depth(value), 3)),
        "max_nodes" => Ok((limits.with_max_nodes(value), 4)),
        "max_storage_bytes" => Ok((limits.with_max_storage_bytes(value), 5)),
        "max_integer_bits" => Ok((limits.with_max_integer_bits(value), 6)),
        "max_exponent" => Ok((limits.with_max_exponent(value), 7)),
        "max_frames" => Ok((limits.with_max_frames(value), 8)),
        _ => Err("unknown limit: a limit is a field of Limits, such as max_work"),
    }
}

/// The `u64` that `digits` writes in decimal: one or more ASCII digits,
/// without a sign.
fn decimal(digits: &str) -> Result<u64, &'static str> {
    let bytes = digits.as_bytes();
    if bytes.is_empty() {
        return Err("a limit has no value");
    }
    let mut value: u64 = 0;
    let mut index = 0;
    while index < bytes.len() {
        let byte = bytes[index];
        if !byte.is_ascii_digit() {
            return Err("a limit value is not decimal digits");
        }
        value = match append_digit(value, u64::from(byte - b'0')) {
            Some(value) => value,
            None => return Err("a limit value does not fit in 64 bits"),
        };
        index += 1;
    }
    Ok(value)
}

/// `value` with the decimal digit `digit` appended, or `None` beyond
/// `u64::MAX`.
fn append_digit(value: u64, digit: u64) -> Option<u64> {
    match value.checked_mul(10) {
        Some(tens) => tens.checked_add(digit),
        None => None,
    }
}

#[cfg(test)]
mod tests {
    use std::io::BufReader;

    use kalyx::context::{CancelProbe, MonotonicClock};

    use super::*;

    /// A writer that records each call of `write` and each flush.
    #[derive(Default)]
    struct Recorder {
        writes: Vec<Vec<u8>>,
        flushes: usize,
    }

    impl Write for Recorder {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            self.writes.push(buf.to_vec());
            Ok(buf.len())
        }

        fn flush(&mut self) -> std::io::Result<()> {
            self.flushes += 1;
            Ok(())
        }
    }

    /// A writer whose reader has gone, as a closed pipe.
    struct Closed;

    impl Write for Closed {
        fn write(&mut self, _: &[u8]) -> std::io::Result<usize> {
            Err(std::io::Error::from(std::io::ErrorKind::BrokenPipe))
        }

        fn flush(&mut self) -> std::io::Result<()> {
            Err(std::io::Error::from(std::io::ErrorKind::BrokenPipe))
        }
    }

    /// A writer that takes every write but fails to flush, as a pipe whose
    /// reader goes away before the buffered line reaches it.
    struct FlushFails;

    impl Write for FlushFails {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            Ok(buf.len())
        }

        fn flush(&mut self) -> std::io::Result<()> {
            Err(std::io::Error::from(std::io::ErrorKind::BrokenPipe))
        }
    }

    /// A probe that reports a cancellation from its poll number `at` on,
    /// counting from 0.
    struct CancelAt {
        at: u64,
        polls: u64,
    }

    impl CancelProbe for CancelAt {
        fn is_cancelled(&mut self) -> bool {
            let cancelled = self.polls >= self.at;
            self.polls += 1;
            cancelled
        }

        fn fork(&self) -> Box<dyn CancelProbe> {
            Box::new(Self {
                at: self.at,
                polls: self.polls,
            })
        }
    }

    /// A context with the default limits whose probe reports a
    /// cancellation from its poll number `at` on.
    fn cancelled_at(at: u64) -> Context {
        Context::with_observers(
            Limits::new(),
            Box::new(MonotonicClock::new()),
            Box::new(CancelAt { at, polls: 0 }),
        )
    }

    /// The line of `request` that the library gives under `limits`, with the
    /// fallback step, computed without the program.
    fn library_line(request: &Request, limits: Limits) -> Option<Vec<u8>> {
        let mut context = Context::new(limits, CancelFlag::new());
        let outcome = execute(request, &mut context);
        match serialize(&outcome, &mut context) {
            Ok(line) => Some(line),
            Err(_) if outcome.result().is_err() => serialize(
                &outcome,
                &mut Context::new(Limits::new(), CancelFlag::new()),
            )
            .ok(),
            Err(_) => None,
        }
    }

    /// Whether `bytes` is one whole line: it ends with its only line feed.
    fn is_whole_line(bytes: &[u8]) -> bool {
        bytes.last() == Some(&b'\n') && bytes.iter().filter(|&&byte| byte == b'\n').count() == 1
    }

    #[test]
    fn a_request_writes_its_line_with_one_write_and_a_flush() {
        let request = Request::new("expand", "x", "(x + 1)^2");
        let mut out = Recorder::default();
        let reply = respond(
            &request,
            &mut Context::new(Limits::new(), CancelFlag::new()),
            &mut out,
        );
        assert_eq!(reply, Reply::Answered);
        assert_eq!(out.writes, [b"value\t0\t0\t0\t1 + 2*x + x^2\n".to_vec()]);
        assert_eq!(out.flushes, 1);
    }

    #[test]
    fn a_cancelled_request_writes_its_error_line_whole() {
        let flag = CancelFlag::new();
        flag.cancel();
        let request = Request::new("eval", "x", "1/3 + 1/6");
        let mut out = Recorder::default();
        let reply = respond(&request, &mut Context::new(Limits::new(), flag), &mut out);
        assert_eq!(reply, Reply::Failed);
        assert_eq!(out.writes.len(), 1);
        assert!(out.writes[0].starts_with(b"error\t0\t0\t0\tCancelled\t"));
        assert!(is_whole_line(&out.writes[0]));
    }

    #[test]
    fn a_cancellation_at_any_charge_point_leaves_the_whole_line_or_nothing() {
        let request = Request::new("expand", "x", "(x + 1)^5");
        let value = b"value\t0\t0\t0\t1 + 5*x + 10*x^2 + 10*x^3 + 5*x^4 + x^5\n";
        let (mut errors, mut unwritten) = (0, 0);
        let mut at = 0;
        loop {
            assert!(at < 100_000, "the request never completed");
            let mut out = Recorder::default();
            let reply = respond(&request, &mut cancelled_at(at), &mut out);
            match reply {
                Reply::Answered => {
                    assert_eq!(out.writes, [value.to_vec()]);
                    break;
                }
                Reply::Failed => {
                    // Cancelled during the work: the error line, whole, from
                    // the fallback step.
                    assert_eq!(out.writes.len(), 1);
                    assert!(out.writes[0].starts_with(b"error\t0\t0\t0\tCancelled\t"));
                    assert!(is_whole_line(&out.writes[0]));
                    errors += 1;
                }
                Reply::Unwritten => {
                    // Cancelled while the value line was built: nothing.
                    assert!(out.writes.is_empty());
                    assert_eq!(out.flushes, 0);
                    unwritten += 1;
                }
                Reply::WriteFailed => panic!("the recorder never fails"),
            }
            at += 1;
        }
        assert!(errors > 0, "no cancellation fell into the work");
        assert!(unwritten > 0, "no cancellation fell into the line");
    }

    #[test]
    fn a_value_whose_line_exceeds_its_limits_is_not_written() {
        let request = Request::new("eval", "x", "1/3 + 1/6");
        let limits = Limits::new().with_max_output_bytes(5);
        let mut out = Recorder::default();
        let reply = respond(
            &request,
            &mut Context::new(limits, CancelFlag::new()),
            &mut out,
        );
        assert_eq!(reply, Reply::Unwritten);
        assert!(out.writes.is_empty());
        assert_eq!(library_line(&request, limits), None);
    }

    #[test]
    fn an_error_whose_line_exceeds_its_limits_takes_the_fallback_step() {
        let request = Request::new("eval", "x", "0*(1/0)");
        let limits = Limits::new().with_max_output_bytes(5);
        let mut out = Recorder::default();
        let reply = respond(
            &request,
            &mut Context::new(limits, CancelFlag::new()),
            &mut out,
        );
        assert_eq!(reply, Reply::Failed);
        let expected = library_line(&request, limits).unwrap();
        assert!(expected.starts_with(b"error\t0\t0\t0\tDivisionByZero\t3..6\t"));
        assert_eq!(out.writes, [expected]);
    }

    #[test]
    fn a_failed_write_is_reported_and_never_panics() {
        let request = Request::new("eval", "x", "1");
        let mut context = Context::new(Limits::new(), CancelFlag::new());
        assert_eq!(
            respond(&request, &mut context, &mut Closed),
            Reply::WriteFailed
        );
        assert_eq!(status_of(&Reply::WriteFailed, None), STREAM_FAILED);
        // A line that is written but cannot be flushed fails as well.
        let mut context = Context::new(Limits::new(), CancelFlag::new());
        assert_eq!(
            respond(&request, &mut context, &mut FlushFails),
            Reply::WriteFailed
        );
    }

    #[test]
    fn replies_map_to_exit_statuses() {
        assert_eq!(status_of(&Reply::Answered, None), SUCCESS);
        assert_eq!(status_of(&Reply::Failed, Some(1)), REQUEST_FAILED);
        assert_eq!(status_of(&Reply::Unwritten, Some(2)), REQUEST_FAILED);
        assert_eq!(status_of(&Reply::WriteFailed, Some(3)), STREAM_FAILED);
    }

    /// The lines that `read_line` reads from `input` through a buffer of
    /// `capacity` bytes.
    fn read_all(input: &[u8], capacity: usize) -> Vec<Vec<u8>> {
        let mut reader = BufReader::with_capacity(capacity, input);
        let mut line = Vec::new();
        let mut lines = Vec::new();
        loop {
            match read_line(&mut reader, &mut line) {
                LineRead::Line => lines.push(line.clone()),
                LineRead::End => return lines,
                LineRead::Failed => panic!("reading a slice never fails"),
            }
        }
    }

    #[test]
    fn lines_are_read_with_or_without_a_last_line_feed() {
        for capacity in [1, 2, 3, 64] {
            let expected = [b"eval".to_vec(), b"".to_vec(), b"x\ty".to_vec()];
            assert_eq!(read_all(b"eval\n\nx\ty\n", capacity), expected);
            assert_eq!(read_all(b"eval\n\nx\ty", capacity), expected);
            assert!(read_all(b"", capacity).is_empty());
            assert_eq!(read_all(b"\n", capacity), [Vec::<u8>::new()]);
        }
    }

    #[test]
    fn a_line_holds_up_to_four_fields_and_the_missing_ones_are_empty() {
        let (request, limits) = request_of_line(b"expand\tx\t(x+1)^2\tmax_work=9").unwrap();
        assert_eq!(request, Request::new("expand", "x", "(x+1)^2"));
        assert_eq!(limits, Limits::new().with_max_work(9));
        let (request, limits) = request_of_line(b"diff\tt\tt^3\r").unwrap();
        assert_eq!(request, Request::new("diff", "t", "t^3"));
        assert_eq!(limits, Limits::new());
        let (request, _) = request_of_line(b"eval").unwrap();
        assert_eq!(request, Request::new("eval", "", ""));
        let (request, _) = request_of_line(b"").unwrap();
        assert_eq!(request, Request::new("", "", ""));
        let (request, limits) = request_of_line(b"eval\t\t1 + 2\t").unwrap();
        assert_eq!(request, Request::new("eval", "", "1 + 2"));
        assert_eq!(limits, Limits::new());
    }

    #[test]
    fn a_line_that_is_not_a_request_is_rejected() {
        assert!(request_of_line(b"eval\tx\t1\t-\textra").is_err());
        assert!(request_of_line(b"eval\tx\t\xff").is_err());
        assert!(request_of_line(b"eval\tx\t1\tmax_wrk=1").is_err());
    }

    #[test]
    fn limits_take_the_format_of_the_answer_vectors() {
        assert_eq!(limits_of("-"), Ok(Limits::new()));
        assert_eq!(limits_of(""), Ok(Limits::new()));
        assert_eq!(
            limits_of("max_depth=32;max_work=18446744073709551615"),
            Ok(Limits::new().with_max_depth(32).with_max_work(u64::MAX))
        );
        let every = "max_work=1;max_input_bytes=2;max_output_bytes=3;max_depth=4;max_nodes=5;\
                     max_storage_bytes=6;max_integer_bits=7;max_exponent=8;max_frames=9";
        let expected = Limits::new()
            .with_max_work(1)
            .with_max_input_bytes(2)
            .with_max_output_bytes(3)
            .with_max_depth(4)
            .with_max_nodes(5)
            .with_max_storage_bytes(6)
            .with_max_integer_bits(7)
            .with_max_exponent(8)
            .with_max_frames(9);
        assert_eq!(limits_of(every), Ok(expected));
    }

    #[test]
    fn invalid_limits_are_rejected() {
        for spec in [
            "max_work",
            "max_work=",
            "max_work=+5",
            "max_work=-1",
            "max_work=1x",
            "max_work=18446744073709551616",
            "max_work=1;max_work=2",
            "max_work=1;",
            ";max_work=1",
            "bogus=1",
            " max_work=1",
        ] {
            assert!(limits_of(spec).is_err(), "{spec}");
        }
    }

    /// The arguments `texts` as the program receives them.
    fn arguments(texts: &[&str]) -> Vec<OsString> {
        texts.iter().map(OsString::from).collect()
    }

    #[test]
    fn arguments_select_the_mode() {
        assert_eq!(invocation(arguments(&[])), Ok(Invocation::Lines));
        assert_eq!(
            invocation(arguments(&["--version"])),
            Ok(Invocation::Version)
        );
        assert_eq!(invocation(arguments(&["--help"])), Ok(Invocation::Help));
        assert_eq!(invocation(arguments(&["-h"])), Ok(Invocation::Help));
        assert_eq!(
            invocation(arguments(&["eval", "-2"])),
            Ok(Invocation::Single(
                Request::new("eval", "", "-2"),
                Limits::new()
            ))
        );
        assert_eq!(
            invocation(arguments(&[
                "--limits",
                "max_exponent=3",
                "diff",
                "x",
                "x^2"
            ])),
            Ok(Invocation::Single(
                Request::new("diff", "x", "x^2"),
                Limits::new().with_max_exponent(3)
            ))
        );
        // An unknown operation is a request, which the command entry rejects.
        assert_eq!(
            invocation(arguments(&["simplify", "x"])),
            Ok(Invocation::Single(
                Request::new("simplify", "", "x"),
                Limits::new()
            ))
        );
    }

    #[test]
    fn usage_errors_are_rejected() {
        for texts in [
            &["eval"][..],
            &["eval", "x", "1", "2"],
            &["--bogus"],
            &["--version", "eval", "1"],
            &["--limits"],
            &["--limits", "max_work=1"],
            &["--limits", "max_work", "eval", "1"],
        ] {
            assert!(invocation(arguments(texts)).is_err(), "{texts:?}");
        }
    }

    #[cfg(unix)]
    #[test]
    fn an_argument_that_is_not_utf8_is_a_usage_error() {
        use std::os::unix::ffi::OsStringExt;

        let argument = OsString::from_vec(vec![b'1', 0xff]);
        let texts = vec![OsString::from("eval"), argument];
        assert!(invocation(texts).is_err());
    }

    #[test]
    fn the_version_is_that_of_the_package() {
        assert_eq!(
            version_text(),
            format!("kalyx {}\n", env!("CARGO_PKG_VERSION"))
        );
    }
}
