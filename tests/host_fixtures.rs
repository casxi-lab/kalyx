//! The host counterparts of the four cancellation and budget fixtures planned
//! for krepi's calculator worker: the total budget of a job exceeded,
//! cancellation between two evaluations, a deadline that expires on an
//! injected clock, and cancellation in the middle of an evaluation.
//!
//! Each fixture runs a job through `worker`, a host written after the rule
//! for a job of several requests and the fallback step of
//! `docs/components/command/contract.md`, as krepi's planned calculator
//! worker is to run the command entry: one context per request, built with
//! `Context::with_observers` on the clock of the job, its deadline and a
//! cancellation probe; cancellation and the deadline checked between two
//! requests; and every line written to the output, the serial console of
//! the worker, only once `serialize` has returned all of its bytes. Lines
//! are compared by their kind and limit fields, never by their message.
//!
//! krepi's worker, as first planned, does not poll during a request and
//! stops a request that is cancelled in its middle by force;
//! `fixture_mid_evaluation_cancellation` stands in for that stop with a
//! probe that reports the cancellation from one poll of the request on, for
//! every poll in turn, and checks only that no half line is written.

#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    clippy::panic,
    reason = "the helpers of the tests unwrap their results and panic on a malformed line, as the tests do"
)]

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use kalyx::command::serialize;
use kalyx::context::{CancelFlag, CancelProbe, Clock};
use kalyx::{Context, ErrorKind, LimitField, LimitId, Limits, Outcome, Request, Settled, execute};

/// The terminal states of a job.
#[derive(Debug, PartialEq, Eq)]
enum JobState {
    Completed,
    Failed,
    Cancelled,
    ResourceExhausted,
}

/// A clock that advances by one nanosecond at every reading, from 1, and
/// counts its readings; its clones share the count.
#[derive(Clone, Default)]
struct TickingClock {
    reads: Arc<AtomicU64>,
}

impl TickingClock {
    fn reads(&self) -> u64 {
        self.reads.load(Ordering::SeqCst)
    }
}

impl Clock for TickingClock {
    fn now(&mut self) -> u64 {
        self.reads.fetch_add(1, Ordering::SeqCst) + 1
    }

    fn fork(&self) -> Box<dyn Clock> {
        Box::new(self.clone())
    }
}

/// A probe that counts its polls and reports cancellation from the poll
/// after the first `cancel_after` polls on, as a cancel request that arrives
/// in the middle of a request and that its context polls.
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

/// A job of the worker: its requests, the total work that they may charge
/// together and its deadline on the clock of the job.
struct Job<'a> {
    requests: &'a [Request],
    budget: u64,
    deadline: u64,
}

/// What the worker did: the outcome of every request that ran, the bytes it
/// wrote to its output, the work that the requests charged and the terminal
/// state of the job.
struct Run {
    outcomes: Vec<Outcome>,
    output: Vec<u8>,
    work: u64,
    state: JobState,
}

/// The worker. Before request `i` it calls `between(i)`, which stands for
/// what arrives between two evaluations, then checks cancellation of `flag`
/// and the deadline of the job on `clock`. The context of the request has
/// `max_work` set to the work left of the total budget of the job, a copy of
/// `clock`, the deadline of the job and the probe `probe(i)`. The line of
/// the outcome is written to the output when `serialize` returns it under
/// the context of the request; when that fails, the line of an error is
/// written under a fresh context by the fallback step, and a value or a
/// state is not written. The job stops at a cancellation or a passed
/// deadline, and goes on after a fault or a `ResourceLimit`.
fn worker(
    job: &Job<'_>,
    clock: &TickingClock,
    flag: &CancelFlag,
    probe: &dyn Fn(usize) -> Box<dyn CancelProbe>,
    between: &mut dyn FnMut(usize),
) -> Run {
    let mut run = Run {
        outcomes: Vec::new(),
        output: Vec::new(),
        work: 0,
        state: JobState::Completed,
    };
    let mut failed = false;
    for (index, request) in job.requests.iter().enumerate() {
        between(index);
        if flag.is_cancelled() {
            run.state = JobState::Cancelled;
            return run;
        }
        if clock.clone().now() >= job.deadline {
            run.state = JobState::ResourceExhausted;
            return run;
        }
        let limits = Limits::new().with_max_work(job.budget.saturating_sub(run.work));
        let mut c = Context::with_observers(limits, Box::new(clock.clone()), probe(index))
            .with_deadline(job.deadline);
        let outcome = execute(request, &mut c);
        let mut errors = Vec::new();
        if let Err(error) = outcome.result() {
            errors.push(error.kind());
        }
        match serialize(&outcome, &mut c) {
            Ok(line) => run.output.extend_from_slice(&line),
            Err(error) => {
                errors.push(error.kind());
                if outcome.result().is_err() {
                    let fresh = &mut Context::new(Limits::new(), CancelFlag::new());
                    let line = serialize(&outcome, fresh).expect("an error line fits");
                    run.output.extend_from_slice(&line);
                }
            }
        }
        run.work += c.work_used();
        run.outcomes.push(outcome);
        let cancelled = errors.contains(&ErrorKind::Cancelled);
        if cancelled || errors.contains(&ErrorKind::DeadlineExceeded) {
            run.state = if cancelled || flag.is_cancelled() {
                JobState::Cancelled
            } else {
                JobState::ResourceExhausted
            };
            return run;
        }
        failed |= !errors.is_empty();
    }
    if failed {
        run.state = JobState::Failed;
    }
    run
}

/// The probe of a worker that does not poll the job service during a
/// request: one that never reports a cancellation.
fn never(_: usize) -> Box<dyn CancelProbe> {
    Box::new(CountingProbe::after(u64::MAX))
}

/// The lines of an output, each with its line feed; fails on bytes after
/// the last line feed, which would be half a line.
fn whole_lines(output: &[u8]) -> Vec<&str> {
    let text = std::str::from_utf8(output).expect("the output is UTF-8");
    let lines: Vec<&str> = text.split_inclusive('\n').collect();
    for line in &lines {
        assert!(line.ends_with('\n'), "half a line: {line:?}");
        let fields = line.split('\t').count();
        assert!(
            (line.starts_with("value\t") && fields == 5)
                || (line.starts_with("error\t") && fields == 11),
            "not a whole line: {line:?}"
        );
    }
    lines
}

/// The kind of each line of an output, `value` or the kind of an error, and
/// the limit field of an error line.
fn kinds(output: &[u8]) -> Vec<(String, String)> {
    whole_lines(output)
        .into_iter()
        .map(|line| {
            let fields: Vec<&str> = line.trim_end_matches('\n').split('\t').collect();
            if fields[0] == "value" {
                ("value".to_owned(), "-".to_owned())
            } else {
                (fields[4].to_owned(), fields[6].to_owned())
            }
        })
        .collect()
}

/// The kind of a line and its limit field, as `kinds` gives them.
fn kind(kind: &str, limit: &str) -> (String, String) {
    (kind.to_owned(), limit.to_owned())
}

/// The work that `request` charges on its own, with its line.
fn work_of(request: &Request) -> u64 {
    let c = &mut Context::new(Limits::new(), CancelFlag::new());
    let outcome = execute(request, c);
    serialize(&outcome, c).unwrap();
    c.work_used()
}

// Total budget exceeded. The job may charge 400 units of work more than its
// first request needs, so the second, `expand` of `(x+1)^60`, runs with
// `max_work` set to those 400 units, exhausts it and ends with
// `ResourceLimit` naming `max_work`. Its error line is published by the
// fallback step, after the value line of the first; the requests charge no
// more than the total budget, and the job is `failed`, since a
// `ResourceLimit` is a limit of its request.
#[test]
fn fixture_total_budget_exceeded() {
    let requests = [
        Request::new("diff", "x", "(x+1)^5"),
        Request::new("expand", "x", "(x+1)^60"),
    ];
    let first = work_of(&requests[0]);
    assert!(work_of(&requests[1]) > 400);
    let job = Job {
        requests: &requests,
        budget: first + 400,
        deadline: u64::MAX,
    };
    let run = worker(
        &job,
        &TickingClock::default(),
        &CancelFlag::new(),
        &never,
        &mut |_| {},
    );
    assert_eq!(run.state, JobState::Failed);
    assert_eq!(
        kinds(&run.output),
        [kind("value", "-"), kind("ResourceLimit", "Field(max_work)")]
    );
    let error = run.outcomes[1].result().as_ref().unwrap_err();
    assert_eq!(error.kind(), ErrorKind::ResourceLimit);
    assert_eq!(
        error.exceeded().unwrap().id(),
        &LimitId::Field(LimitField::Work)
    );
    assert!(run.work <= job.budget, "{} > {}", run.work, job.budget);
}

// Cancellation between two evaluations. A cancel request arrives after the
// first request has written its line and before the second starts: the
// worker sees it between the two, the second and third requests never run,
// and the job is `cancelled` with the line of the first only.
#[test]
fn fixture_cancellation_between_two_evaluations() {
    let requests = [
        Request::new("eval", "x", "1/3 + 1/6"),
        Request::new("expand", "x", "(x+1)^4"),
        Request::new("diff", "x", "x^2"),
    ];
    let job = Job {
        requests: &requests,
        budget: u64::MAX,
        deadline: u64::MAX,
    };
    let flag = CancelFlag::new();
    let cancel = flag.clone();
    let run = worker(
        &job,
        &TickingClock::default(),
        &flag,
        &never,
        &mut |index| {
            if index == 1 {
                cancel.cancel();
            }
        },
    );
    assert_eq!(run.state, JobState::Cancelled);
    assert_eq!(run.outcomes.len(), 1);
    assert_eq!(run.output, b"value\t0\t0\t0\t1/2\n");
}

// Deadline expiry on an injected clock. The clock of the job advances by
// one at every reading. With the deadline 21 readings after the start of
// the second request, it passes in the middle of that request, which ends
// with `DeadlineExceeded` at a charge point and has its line by the
// fallback step; the third request never runs, and the job is
// `resource_exhausted`. With the deadline one reading after the first
// request, the worker sees it between the two requests, and only the line
// of the first is written.
#[test]
fn fixture_deadline_expiry() {
    let requests = [
        Request::new("eval", "x", "1/0"),
        Request::new("expand", "x", "(x+1)^60"),
        Request::new("eval", "x", "1"),
    ];
    let unbounded = Job {
        requests: &requests[..1],
        budget: u64::MAX,
        deadline: u64::MAX,
    };
    let clock = TickingClock::default();
    worker(&unbounded, &clock, &CancelFlag::new(), &never, &mut |_| {});
    let first = clock.reads();

    let job = Job {
        requests: &requests,
        budget: u64::MAX,
        deadline: first + 1 + 21,
    };
    let run = worker(
        &job,
        &TickingClock::default(),
        &CancelFlag::new(),
        &never,
        &mut |_| {},
    );
    assert_eq!(run.state, JobState::ResourceExhausted);
    assert_eq!(
        kinds(&run.output),
        [kind("DivisionByZero", "-"), kind("DeadlineExceeded", "-")]
    );
    assert_eq!(run.outcomes.len(), 2);

    let job = Job {
        deadline: first + 1,
        ..job
    };
    let run = worker(
        &job,
        &TickingClock::default(),
        &CancelFlag::new(),
        &never,
        &mut |_| {},
    );
    assert_eq!(run.state, JobState::ResourceExhausted);
    assert_eq!(kinds(&run.output), [kind("DivisionByZero", "-")]);
}

// Cancellation in the middle of an evaluation. The probe of the request
// reports a cancellation from the poll after its first k polls on, for
// every k before the end of the request and its line. The output never
// holds half a line: when the request is cancelled during its evaluation,
// the output is exactly the whole `Cancelled` line that the fallback step
// writes, and when it is cancelled while its value line is being written,
// the output is empty, since `serialize` returns no bytes and a value is
// never written again. Uncancelled, the output is the whole value line.
#[test]
fn fixture_mid_evaluation_cancellation() {
    let request = [Request::new("expand", "x", "(x+1)^5")];
    let job = Job {
        requests: &request,
        budget: u64::MAX,
        deadline: u64::MAX,
    };
    let counting = CountingProbe::after(u64::MAX);
    let c = &mut Context::with_observers(
        Limits::new(),
        Box::new(TickingClock::default()),
        Box::new(counting.clone()),
    );
    let outcome = execute(&request[0], c);
    assert!(matches!(outcome.result(), Ok(Settled::Value(_))));
    let evaluation = counting.polls();
    let full = serialize(&outcome, c).unwrap();
    let total = counting.polls();
    assert!(
        evaluation > 10 && total > evaluation + 5,
        "{evaluation} {total}"
    );

    let flag = CancelFlag::new();
    let uncancelled = worker(&job, &TickingClock::default(), &flag, &never, &mut |_| {});
    assert_eq!(uncancelled.output, full);
    assert_eq!(uncancelled.state, JobState::Completed);

    let mut cancelled_lines = 0;
    for k in 0..total {
        let probe = move |_: usize| -> Box<dyn CancelProbe> { Box::new(CountingProbe::after(k)) };
        let run = worker(&job, &TickingClock::default(), &flag, &probe, &mut |_| {});
        assert_eq!(run.state, JobState::Cancelled, "poll {k}");
        whole_lines(&run.output);
        if k < evaluation {
            assert_eq!(kinds(&run.output), [kind("Cancelled", "-")], "poll {k}");
            cancelled_lines += 1;
        } else {
            assert!(run.output.is_empty(), "poll {k}: {:?}", run.output);
        }
    }
    assert_eq!(cancelled_lines, evaluation);
}
