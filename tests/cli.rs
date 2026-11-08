//! The command-line program, run as a process: argument mode for each
//! operation, line mode with and without a line feed after the last line,
//! the exit statuses, usage errors, a closed standard output, a standard
//! input that cannot be read, `--version`, and the replay of every case of
//! `vectors/r02.tsv` through line mode, compared byte for byte with the
//! lines of the command entry. The forms, the line format and the exit
//! statuses are those of `docs/semantics.md`.

#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    clippy::panic,
    reason = "the helpers of the tests unwrap their results and panic on a malformed case, as the tests do"
)]

use std::io::Write;
use std::process::{Command, Output, Stdio};

use kalyx::command::serialize;
use kalyx::context::CancelFlag;
use kalyx::{Context, Limits, Request, execute};

const VECTORS: &str = include_str!("../vectors/r02.tsv");

/// The program built from this package.
const PROGRAM: &str = env!("CARGO_BIN_EXE_kalyx");

/// Runs the program with `arguments` and `input` on its standard input.
fn run(arguments: &[&str], input: &[u8]) -> Output {
    let mut child = Command::new(PROGRAM)
        .args(arguments)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("the program starts");
    let mut stdin = child.stdin.take().expect("standard input is piped");
    let input = input.to_vec();
    // A thread writes the input, so that a large output cannot block it.
    let writer = std::thread::spawn(move || {
        // The program may end before it reads all of its input.
        let _ = stdin.write_all(&input);
    });
    let output = child.wait_with_output().expect("the program ends");
    writer.join().expect("the writer ends");
    output
}

/// The exit status of `output`.
fn status(output: &Output) -> i32 {
    output
        .status
        .code()
        .expect("the program exits with a status")
}

/// Standard error of `output` as text.
fn stderr(output: &Output) -> String {
    String::from_utf8(output.stderr.clone()).expect("standard error is UTF-8")
}

/// Asserts that standard error of `output` holds no panic message.
fn assert_no_panic(output: &Output) {
    let text = stderr(output);
    assert!(!text.contains("panicked"), "{text}");
}

#[test]
fn argument_mode_runs_each_operation() {
    let output = run(&["eval", "1/3 + 1/6"], b"");
    assert_eq!(status(&output), 0);
    assert_eq!(output.stdout, b"value\t0\t0\t0\t1/2\n");
    assert!(output.stderr.is_empty());

    let output = run(&["expand", "x", "(x + 1)^3"], b"");
    assert_eq!(status(&output), 0);
    assert_eq!(output.stdout, b"value\t0\t0\t0\t1 + 3*x + 3*x^2 + x^3\n");

    let output = run(&["diff", "t", "t^3 - 2*t"], b"");
    assert_eq!(status(&output), 0);
    assert_eq!(output.stdout, b"value\t0\t0\t0\t-2 + 3*t^2\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn argument_mode_writes_an_error_line_and_exits_with_1() {
    let output = run(&["eval", "1/0"], b"");
    assert_eq!(status(&output), 1);
    assert!(
        output
            .stdout
            .starts_with(b"error\t0\t0\t0\tDivisionByZero\t0..3\t-\t-\t-\t-\t")
    );
    assert!(output.stderr.is_empty());

    // An operation that the command entry does not have is a request that
    // fails, never a fallback to another operation.
    let output = run(&["simplify", "x"], b"");
    assert_eq!(status(&output), 1);
    assert!(
        output
            .stdout
            .starts_with(b"error\t0\t0\t0\tUnsupported\t-\t-\t-\t-\t-\t")
    );
}

#[test]
fn argument_mode_takes_limits() {
    let output = run(&["--limits", "max_exponent=4", "expand", "x", "x^5"], b"");
    assert_eq!(status(&output), 1);
    assert!(output.stdout.starts_with(
        b"error\t0\t0\t0\tResourceLimit\t2..3\tField(max_exponent)\t-\t4\tRequired(5)\t"
    ));

    // A value line that does not fit its limits is not written.
    let output = run(&["--limits", "max_output_bytes=5", "eval", "1"], b"");
    assert_eq!(status(&output), 1);
    assert!(output.stdout.is_empty());
    assert!(stderr(&output).starts_with("kalyx: "));
}

#[test]
fn usage_errors_exit_with_2_and_write_no_line() {
    for arguments in [
        &["eval"][..],
        &["eval", "x", "1", "2"],
        &["--bogus"],
        &["--limits"],
        &["--limits", "max_work=1"],
        &["--limits", "max_wrk=1", "eval", "1"],
        &["--version", "extra"],
    ] {
        let output = run(arguments, b"");
        assert_eq!(status(&output), 2, "{arguments:?}");
        assert!(output.stdout.is_empty(), "{arguments:?}");
        let text = stderr(&output);
        assert!(text.starts_with("kalyx: "), "{text}");
        assert!(text.contains("Usage: kalyx"), "{text}");
    }
}

#[test]
fn help_writes_the_usage_to_standard_output() {
    let output = run(&["--help"], b"");
    assert_eq!(status(&output), 0);
    assert!(output.stdout.starts_with(b"Usage: kalyx"));
}

#[test]
fn version_writes_the_package_version() {
    let output = run(&["--version"], b"");
    assert_eq!(status(&output), 0);
    let expected = format!("kalyx {}\n", env!("CARGO_PKG_VERSION"));
    assert_eq!(output.stdout, expected.as_bytes());
    assert!(output.stderr.is_empty());
}

#[test]
fn line_mode_answers_every_line() {
    let input = b"eval\tx\t1/3 + 1/6\nexpand\tx\t(x+1)^2\ndiff\tx\tx^3\t-\n";
    let output = run(&[], input);
    assert_eq!(status(&output), 0);
    assert_eq!(
        output.stdout,
        b"value\t0\t0\t0\t1/2\nvalue\t0\t0\t0\t1 + 2*x + x^2\nvalue\t0\t0\t0\t3*x^2\n"
    );
    assert!(output.stderr.is_empty());
}

#[test]
fn line_mode_reads_a_last_line_without_a_line_feed() {
    let output = run(&[], b"eval\tx\t2^10\r\ndiff\tx\tx^2 + x");
    assert_eq!(status(&output), 0);
    assert_eq!(
        output.stdout,
        b"value\t0\t0\t0\t1024\nvalue\t0\t0\t0\t1 + 2*x\n"
    );
}

#[test]
fn line_mode_reports_errors_and_goes_on() {
    // A failing request has its error line; a line that is not a request
    // has a diagnostic and no line; the run goes on and its status is the
    // highest of its lines.
    let input = b"eval\tx\t1/0\neval\tx\t1\t-\textra\neval\tx\t2\n";
    let output = run(&[], input);
    assert_eq!(status(&output), 2);
    let text = String::from_utf8(output.stdout.clone()).unwrap();
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(lines.len(), 2);
    assert!(lines[0].starts_with("error\t0\t0\t0\tDivisionByZero\t"));
    assert_eq!(lines[1], "value\t0\t0\t0\t2");
    assert!(stderr(&output).starts_with("kalyx: line 2: "));

    let output = run(&[], b"eval\tx\t1/0\neval\tx\t2\n");
    assert_eq!(status(&output), 1);
    assert!(output.stderr.is_empty());

    // An empty input has no request.
    let output = run(&[], b"");
    assert_eq!(status(&output), 0);
    assert!(output.stdout.is_empty());
}

#[test]
fn a_closed_standard_output_exits_with_3_without_a_panic() {
    let mut child = Command::new(PROGRAM)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("the program starts");
    // Close the reading end of standard output before the program writes.
    drop(child.stdout.take());
    let mut stdin = child.stdin.take().expect("standard input is piped");
    // The program may end before it reads all of its input.
    let _ = stdin.write_all(b"eval\tx\t1\neval\tx\t2\n");
    drop(stdin);
    let output = child.wait_with_output().expect("the program ends");
    assert_eq!(status(&output), 3);
    assert_no_panic(&output);
    assert!(stderr(&output).contains("kalyx: cannot write to standard output"));
}

#[test]
fn a_write_failure_stops_line_mode_at_once() {
    let mut child = Command::new(PROGRAM)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("the program starts");
    // Close the reading end of standard output before any input is written,
    // so that the first write fails.
    drop(child.stdout.take());
    let mut stdin = child.stdin.take().expect("standard input is piped");
    // The program may end before it reads all of its input.
    let _ = stdin.write_all(b"eval\tx\t1\neval\tx\t2\neval\tx\t3\n");
    drop(stdin);
    let output = child.wait_with_output().expect("the program ends");
    assert_eq!(status(&output), 3);
    assert_no_panic(&output);
    // One diagnostic: the run ended at the first failed write.
    assert_eq!(
        stderr(&output)
            .matches("cannot write to standard output")
            .count(),
        1
    );
}

#[test]
fn version_and_help_to_a_closed_pipe_exit_with_3() {
    for argument in ["--version", "--help"] {
        let (reader, writer) = std::io::pipe().expect("a pipe");
        drop(reader);
        let output = Command::new(PROGRAM)
            .arg(argument)
            .stdout(writer)
            .stderr(Stdio::piped())
            .output()
            .expect("the program runs");
        assert_eq!(status(&output), 3, "{argument}");
        assert_no_panic(&output);
        assert!(
            stderr(&output).contains("kalyx: cannot write to standard output"),
            "{argument}"
        );
    }
}

#[cfg(unix)]
#[test]
fn a_read_failure_exits_with_3() {
    // A directory opens but cannot be read, so the first read fails.
    let directory = std::fs::File::open("/").expect("the root directory opens");
    let output = Command::new(PROGRAM)
        .stdin(Stdio::from(directory))
        .output()
        .expect("the program runs");
    assert_eq!(status(&output), 3);
    assert!(output.stdout.is_empty());
    assert_no_panic(&output);
    assert!(stderr(&output).contains("kalyx: cannot read standard input"));
}

/// The limits of the `limits` column of a vector: `-`, or `field=value`
/// settings separated by `;`.
fn vector_limits(column: &str) -> Limits {
    let mut limits = Limits::new();
    if column == "-" {
        return limits;
    }
    for setting in column.split(';') {
        let (field, value) = setting.split_once('=').expect("a setting has `=`");
        let value: u64 = value.parse().expect("a limit is a u64");
        limits = match field {
            "max_work" => limits.with_max_work(value),
            "max_input_bytes" => limits.with_max_input_bytes(value),
            "max_output_bytes" => limits.with_max_output_bytes(value),
            "max_depth" => limits.with_max_depth(value),
            "max_nodes" => limits.with_max_nodes(value),
            "max_storage_bytes" => limits.with_max_storage_bytes(value),
            "max_integer_bits" => limits.with_max_integer_bits(value),
            "max_exponent" => limits.with_max_exponent(value),
            "max_frames" => limits.with_max_frames(value),
            _ => panic!("unknown limit {field}"),
        };
    }
    limits
}

/// The line that the command entry gives for `request` under `limits`, with
/// the fallback step of its contract; `None` for a value or a state whose
/// line fails.
fn entry_line(request: &Request, limits: Limits) -> Option<Vec<u8>> {
    let mut context = Context::new(limits, CancelFlag::new());
    let outcome = execute(request, &mut context);
    match serialize(&outcome, &mut context) {
        Ok(line) => Some(line),
        Err(_) if outcome.result().is_err() => {
            let mut fresh = Context::new(Limits::new(), CancelFlag::new());
            Some(serialize(&outcome, &mut fresh).expect("the fallback line"))
        }
        Err(_) => None,
    }
}

#[test]
fn every_vector_of_r02_replays_through_line_mode_byte_for_byte() {
    let mut input = Vec::new();
    let mut expected = Vec::new();
    let mut cases = 0;
    let mut limited = 0;
    let mut failures = 0;
    for row in VECTORS.lines().skip(1) {
        let columns: Vec<&str> = row.split('\t').collect();
        let [_id, operation, variable, text, result, _answer, limits] = columns[..] else {
            panic!("a case has seven columns: {row}");
        };
        let line = format!("{operation}\t{variable}\t{text}\t{limits}\n");
        input.extend_from_slice(line.as_bytes());
        let request = Request::new(operation, variable, text);
        let entry = entry_line(&request, vector_limits(limits)).expect("every case has a line");
        assert_eq!(entry.starts_with(b"value\t"), result == "ok", "{row}");
        expected.extend_from_slice(&entry);
        cases += 1;
        limited += usize::from(limits != "-");
        failures += usize::from(result != "ok");
    }
    assert_eq!(cases, 58);
    assert_eq!(limited, 4);
    assert!(failures > 0);
    let output = run(&[], &input);
    assert_eq!(
        String::from_utf8(output.stdout.clone()).unwrap(),
        String::from_utf8(expected.clone()).unwrap()
    );
    assert_eq!(output.stdout, expected);
    assert_eq!(status(&output), 1);
    assert!(output.stderr.is_empty(), "{}", stderr(&output));
}
