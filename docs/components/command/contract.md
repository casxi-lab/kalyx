# Command entry

**Co-signed.** krepi, whose job service runs the command entry, co-signed
this contract on 2026-11-07: the shapes of the request and the outcome, the
output lines, the two tables, of the
[terminal states of a job](#table-1-outcomes-and-the-terminal-states-of-a-job)
and of [who enforces each limit](#table-2-the-limits-and-who-enforces-them),
the rule for [a job of several requests](#a-job-of-several-requests) and
the [fallback step](#the-fallback-line) for the line of a failed request.
After the release `v0.1.0`, a change to Table 1, Table 2, the rule for a job
of several requests or the fallback step needs krepi's co-signature again.

This contract states the command entry of kalyx: the request that a caller
gives it, the one dispatch table of its operations and what each operation
does, the outcome that it returns, and the line bytes that it writes for an
outcome, the only output format of the library; how a request is charged and
bounded, its deadline and cancellation, and how its outcome maps to the
states of a job of krepi, the casξ operating system; the list of the public
names of the crate root and the allocation check. It applies to the module
`src/command.rs` with its submodules in `src/command/`, to
`api/root-names.txt` and to the allocation check in `checks/allocation/`.
The [architecture](../../architecture.md#release-01) places the component
among the components of release 0.1, and the
[public API conventions](../../conventions/public-api.md) state the rules
that every public interface follows. The limits, the charges, the deadline
and cancellation belong to the [context](../context/contract.md), the errors
and result states to the [errors and result states](../errors/contract.md),
the input syntax to the [parser](../syntax/contract.md), the terms to the
[term core](../terms/contract.md) and the expansion and differentiation to
the [polynomials](../polynomials/contract.md). The bytes of the output lines
are stated in [the input syntax and semantics](../../semantics.md#output-lines).

**Status.** Implemented in `src/command.rs` and `src/command/`, at tier A1
(tested with a written contract). The command entry is written anew for kalyx
after the design rules of the architecture: no code and no test is taken
over from the earlier implementation, which served as a reference, so
[PORTING](../../../PORTING.md) has no row for it. Its first callers are the
command-line program, `src/main.rs`, and the calculator job of krepi,
built from a pinned commit of the library.

## Scope

- **Included.** The request, with its operation, variable, input, versions
  and settings; the entry `execute`; the dispatch table with `eval`, `expand`
  and `diff`; the outcome, which echoes the versions of its request and holds
  its result or error; `serialize`, which writes an outcome as one line; the
  order of the failures of a request; the mapping of outcomes to the
  terminal states of a job, the rule for a job of several requests and the
  fallback step for the line of a failed request, and the division of the
  limits between kalyx and the host; the list of the public names of the crate root with its test;
  and the allocation check of repeated requests.
- **Excluded, with their owners.**
  - Arguments, standard streams, line mode and process exit codes: the
    command-line program, `src/main.rs`, which builds requests,
    calls `execute` and `serialize` and chooses its exit code
    ([the command-line program](../../semantics.md#the-command-line-program)).
  - Sessions, bindings, a context version that is checked against a
    session, the fault `StaleEnvironment`, nested commands and the commands
    beyond the three of this release: the session and command layer, release
    0.3.
  - Streaming entries with a progress receiver
    ([convention 13](../../conventions/public-api.md#13-request-inputs-and-progress)):
    with their first streaming operation.
  - The comparison of parents with `same_parent` and the fault
    `VariableMismatch`: the coefficient fields of release 0.2, with the first
    parents that can differ.
  - The job service of krepi: its states and their transitions, its worker,
    its resource scope, which bounds real memory, CPU time and the time of a
    job, the forced stop of a job after a grace period, and the race of
    completion and cancellation, which krepi's Job contract fixes.
  - Reading input text, canonical forms, display text, expansion and
    differentiation: the [parser](../syntax/contract.md), the
    [term core](../terms/contract.md) and the
    [polynomials](../polynomials/contract.md).

## Interface

The module `kalyx::command` holds the component, and the crate root
re-exports `Request`, `Outcome` and `execute`:

- `Request`, a `#[non_exhaustive]` record with `Clone`, `Debug`, `PartialEq`
  and `Eq` and these public fields, built by
  `Request::new(operation, variable, input)` with the versions 0 and the
  default settings, and changed with `with_input_version`,
  `with_context_version`, `with_settings` and `with_settings_version`:

  | Field | Type | Meaning |
  | --- | --- | --- |
  | `operation` | `String` | the name of the operation, looked up in the dispatch table |
  | `variable` | `String` | the variable of `expand` and `diff`; `eval` does not read it |
  | `input` | `String` | the input text, in the [input syntax](../../semantics.md) |
  | `input_version` | `u64` | the version of the input, such as the revision of a cell; echoed |
  | `context_version` | `u64` | the version of the computation context of the input, such as a document or a session; echoed and not checked in this release |
  | `settings` | `Settings` | the settings of the request |
  | `settings_version` | `u64` | the version of the settings, such as their revision in a document; echoed |

- `Settings`, a `#[non_exhaustive]` record with no field in this release, with
  `Settings::new()`, `Default`, `Clone`, `Debug`, `PartialEq` and `Eq`. Code
  outside the library cannot write `Settings {}`, so the default is its only
  value; the `compile_fail` documentation test of `Settings` checks this
  (`E0639`).
- `Outcome`, with private fields, built only by `execute`, with the accessors
  `input_version()`, `context_version()`, `settings_version()`, `result()`,
  which returns `&Result<Settled<Term>>`, and `into_result()`; `Clone` and
  `Debug`, and `#[must_use]`.
- `execute(request: &Request, context: &mut Context) -> Outcome`.
- `serialize(outcome: &Outcome, context: &mut Context) -> Result<Vec<u8>>`.

`execute` returns an `Outcome` and not a `Result`, so that the versions of a
request come back with every result and every error; the outcome holds the
`Result<Settled<Term>>` of
[convention 2](../../conventions/public-api.md#2-errors-separate-from-result-states).
Both functions take the context last
([convention 1](../../conventions/public-api.md#1-request-context-last)), and
neither creates one. The component uses only public interfaces of the other
components: `parse`, `PolynomialRing` over `Rationals`, the accessors and
`display` of `Term`, `charge_output` of the context, and the accessors of
`Error` and `LimitExceeded`.

## Rules

### The request and its order

`execute` checks the request in a fixed order and stops at the first
failure, which the outcome holds:

1. **Settings.** Settings other than the default fail with
   `Fault(Unsupported)`, without a span and before any charge. The check
   compares the whole record with its default, so a setting that a later
   release adds is checked without a change of the entry; a value that a
   release supports is accepted from that release on.
2. **Operation.** The name is looked up in the dispatch table, byte for byte:
   no trimming, no case folding and no prefix match. A name that the table
   does not hold, the empty name included, fails with `Fault(Unsupported)`,
   without a span and before any charge. An unknown operation never falls
   back to another operation.
3. **The operation**, which reads the fields that the table names, in the
   order that it states, and charges every step of its work to the context.

The settings, the operation and the variable are request fields, not text of
the input, so their errors have no span. The entry reads the operation name
at most up to the length of the longest name of the table, so the check is
bounded whatever the length of the name.

### The dispatch table

The table names each operation once; a `match` on the operation that the
name gives runs it. These are the operations of this release:

| Operation | Reads | Steps, in order | Result |
| --- | --- | --- | --- |
| `eval` | the input | `parse` of the input; the term must be a number | the number, as a term |
| `expand` | the variable, then the input | the ring $\mathbb{Q}[x]$ of the variable; `parse` of the input; its expansion in the ring; the conversion of the polynomial back to a term | the canonical term of the polynomial |
| `diff` | the variable, then the input | the ring of the variable; `parse` of the input; `differentiate`: the expansion, the derivative by the variable and the conversion back to a term | the canonical term of the derivative |

Every operation of this release returns a value, `Settled::Value` of a term;
none ends in a state.

- **`eval`** reads the canonical term of the input. A number is the result. A
  term that is not a number fails with `Fault(UnknownSymbol)`, without a
  span: the term core evaluates every numeric subterm strictly, so in this
  release a term that is not a number holds a symbol, and no symbol has a
  value in an evaluation. Since the canonical form decides, `x - x` and
  `0*x` are 0, while `x/x` and `0*x^(-1)` keep their witness of $x^{-1}$ and
  `(x+1)^2 - x^2 - 2*x - 1`, whose power of a sum the term core does not
  expand, holds $x$; all three fail. The earlier implementation evaluated the
  syntax of the input and failed at its first symbol with the span of the
  symbol; a term has no span.
- **The variable** of `expand` and `diff` is checked by `PolynomialRing::new`
  with the rule of symbol names of the term core before the input is read:
  a name that is not an ASCII letter or `_` followed by ASCII letters, digits
  and `_`, the empty name included, fails with `Fault(Syntax)`, and a name
  reserved for a constant, `pi`, `i` or `undefined`, with
  `Fault(Unsupported)`, both without a span and before any charge. Then the
  ring charges one unit and one per byte of the name. Names are
  case-sensitive, so `X` is not the variable `x`.
- **`expand` and `diff`** then fail as the
  [expansion](../polynomials/contract.md#expansion) states, in its order of
  failures: `Fault(UnknownSymbol)` for a symbol other than the variable,
  `Fault(NotPolynomial)` for a negative power, and the limits of the degree
  and of the storage of every polynomial; all without a span.

### A missing operand

- **Empty input.** An input that is empty or holds only whitespace has no
  operand. It fails with `Fault(Syntax)` and the empty span at the end of
  the input, for every operation: `parse` finds the end of the input where
  an operand starts. For `expand` and `diff`, a variable that fails comes
  first.
- **Other cases.** An operand that is incomplete, such as `1 +`, `()` or
  `(1`, fails with `Fault(Syntax)` by the rules of the parser, with the span
  of the token where an operand is missing or the empty span at the end. An
  empty operation name is an unknown operation, and an empty variable of
  `expand` or `diff` fails as a malformed variable; `eval` does not read the
  variable, so an empty one changes nothing.
- **No fallback.** The operation and its operand are separate fields of the
  request, so an operation without an operand never becomes an operand
  itself, and an unknown operation never falls back to another operation.
  This corrects a [defect](#defects-of-the-earlier-implementation) of the
  earlier implementation.

### Parents and elements

`expand` and `diff` build their ring from the variable of the request and
convert the polynomial that the ring returns back to a term with that same
ring, before the operation returns; no polynomial outlives its operation,
and an outcome holds terms only. So the entry stores no parent together with
an element, and no check with `same_parent` applies in this release. A
later release that stores such a pair, such as a polynomial in a session,
checks it there, and a mismatch fails with `VariableMismatch`.

### The outcome

- The outcome echoes the input version, the context version and the
  settings version of its request, with every result: a value, a state, a
  fault and a request failure.
- It holds a structured result, `Ok(Settled::Value(term))` or
  `Ok(Settled::State(state))`, or the `Error` that ended the request, with
  its kind, its span into the input and, for `ResourceLimit`, its
  `LimitExceeded`. It holds no process exit code and no text: a program
  chooses its exit code from the outcome, and text comes only from
  `serialize`.
- The context version is echoed and not checked in this release, which has
  no session.

### Output lines

`serialize` writes an outcome as one line of bytes, in the format that
[the output lines](../../semantics.md#output-lines) state: a `value`, `state`
or `error` line, with the three versions after its first field, and for an
error its kind, span, limit, scope, allowed value, amount and escaped
message. It is the only output format of the library
([convention 10](../../conventions/public-api.md#10-bounded-output)): the
command-line program writes its results only through it, and results reach
callers as text only through it, never through `Display`.

### Charging and bounded output

- **`execute`** charges the context as its steps charge it: the ring one unit
  and one per byte of the variable, the parser, the term core and the
  polynomials as their contracts state. It charges no output.
- **`serialize`** charges every byte that it writes with `charge_output`,
  which first checks the request's cumulative `max_output_bytes`, then
  charges one work unit per byte. It writes the line field by field: each
  field with the tab before it is charged and then appended, the display
  text of a value charges its own steps, one unit each, and its pieces, and
  the line feed is charged last. So the output charged for a line is exactly
  its length, and every field is a charge point.
- **No partial output.** The line is returned only when every charge has
  succeeded. A failure returns the error and no bytes; what was charged for
  the fields before it stays charged, as every charge does.
- **Cumulative output.** `max_output_bytes` bounds all the output of the
  request: every line that is written under its context and every display
  of a term.
- **A failed line.** When `serialize` fails, the outcome has no line under
  that context. The error is a request failure of the same request,
  `ResourceLimit` naming `max_output_bytes` or `max_work`, `Cancelled` or
  `DeadlineExceeded`, or an error of the display of a term, such as
  `ResourceLimit` naming `max_integer_bits` of the context. Written under
  the context of the request, it is one of the errors of the request, which
  decide the terminal state of a job as
  [a job of several requests](#a-job-of-several-requests) states.
- **Which outcomes have no line under their own context.** An outcome that
  ended with `Cancelled` or `DeadlineExceeded` never has a line under the
  context of its request: `serialize` polls the same probe, which keeps
  reporting the cancellation, and observes the same expiry, which is final,
  so it fails with the same error. Any other outcome has no line there when
  the work or the output that the request has left is less than its line
  needs. A failed charge does not change the work charged so far, so an
  outcome of `ResourceLimit` on `max_work` has its line when the work left
  is enough: `diff` in a variable of 300 letters `a` with the input `x`,
  under `max_work = 200`, fails at the charge of 301 units for its
  variable with nothing charged, and its error line of 98 bytes is written
  under the context of the request. A fault may have no line: `eval` of
  `0*(1/0)` under `max_work = 24` charges all 24 units before its
  `DivisionByZero`, and its line fails there with `ResourceLimit` naming
  `max_work`.

### The fallback line

A host writes the line of each request that ran in a prescribed step:

1. It writes the line under the context of the request.
2. When that fails and the outcome is an `Err`, of any kind, faults
   included, it writes the line again under
   `Context::new(Limits::new(), CancelFlag::new())`, with a fresh flag and
   no deadline, and the job publishes that line.

An outcome of `Settled::Value` or `Settled::State` is never written again:
under another context its line would escape the request's
`max_output_bytes` and `max_integer_bits`, so it has no line. The fallback
line is only published; the terminal state of the job still follows the
errors of the request, the failure of the line under the request's context
included, as [a job of several requests](#a-job-of-several-requests)
states. The same outcome gives the same bytes under every context, so the
bytes that the job publishes do not depend on where the line was written.
An error line holds no display text: its message is fixed text, to which
`ResourceLimit` adds only the name of a field or a parameter, so in this
release it is far shorter than the default `max_work` of 100,000 units and
`max_output_bytes` of 65,536 bytes allow, and under a fresh flag without a
deadline its writing reports neither `Cancelled` nor `DeadlineExceeded`.

### Determinism

The same request under the same limits charges the same work and gives the
same outcome in every run, on every host, and the same outcome gives the same
line bytes. Neither the outcome nor the line depends on pointer identity,
on whether terms share nodes, on addresses, on hash order or on time; the
numbers of a line are written in decimal, and the display text of a term
depends only on the term
([convention 8](../../conventions/public-api.md#8-determinism)). Only the
outcome of cancellation and of a deadline depends on the injected probe and
clock. The line of a `DeadlineExceeded` outcome depends on the charge point
where the deadline was observed, so byte-identical lines on different hosts
for an outcome of a deadline need an injected clock; requests that are
compared across hosts run without a deadline that can pass, or on such a
clock.

### The deadline and cancellation

- **The entry accepts a deadline and cancellation.** They come with the
  context, which the caller creates for each request with its budget, its
  deadline and its cancellation probe: `Context::new(limits, flag)` with the
  monotonic clock and a `CancelFlag`, or
  `Context::with_observers(limits, clock, probe)` with any clock and any
  probe, then `with_deadline(at)` or `with_timeout(nanos)`. The library never
  creates a context, and the settings and versions of the request are not
  part of it.
- **Inside a request** the checks are cooperative. Every charge point polls
  the cancellation probe first, then observes the deadline on the schedule
  of the context, then checks the work: a cancellation that the probe reports
  is observed at the next charge point, and the work charged after the
  deadline passes is at most $\max(4032, L)$ units plus one primitive
  operation that is running, as the
  [context](../context/contract.md#reading-the-clock) states. A primitive
  operation, such as a multiplication of large integers, an allocation or
  the formatting of a number, is not interrupted.
- **Between requests** the host checks cancellation, then the deadline of
  the job: a worker that runs several requests checks its flag between two
  of them and does not start the next one once it is cancelled or the
  deadline of the job has passed. A request whose context holds a cancelled
  flag fails at its first charge point with `Cancelled`, before any charged
  work; the variable of `expand` and `diff` is read once by the rule of
  symbol names before that charge point. A request that fails before its
  first charge point returns that error and not `Cancelled`: settings other
  than the default, an unknown operation, a malformed or reserved variable,
  and an input over `max_input_bytes`, which the parser checks before it
  reads the input and which is not a charge point. This is why the host
  checks cancellation between two requests itself.
- **The deadline of a job** belongs to the job, not to one request. A
  deadline is a reading of the clock of the context, and `Context::new`
  creates a `MonotonicClock` whose origin is the creation of the context, so
  `with_deadline(at)` on such a context is a deadline of that request only.
  A host that runs several requests converts the deadline of the job to the
  clock of their contexts, in one of two ways: it shares one clock among the
  requests, with
  `Context::with_observers(limits, Box::new(job_clock), Box::new(flag.clone()))`
  and then `with_deadline(job_deadline)`, where `MonotonicClock` is `Copy`
  and its copies share their origin; or it gives each request
  `with_timeout(remaining)`, the time left until the deadline of the job.
- **What the host enforces.** The context bounds work and logical sizes, not
  memory, CPU time or the time of a primitive. A host that needs a hard stop
  runs requests in a process that it can stop as a whole, as krepi stops a
  job by force after its grace period; such a request ends without an
  outcome.

A host that runs the requests of a job one after another can do so as
follows, where `clock` is the clock of the job, `deadline` the deadline of
the job as a reading of that clock, and `flag` the cancellation flag of the
job, which the host may set from any thread. The function implements the
[fallback step](#the-fallback-line) and, as far as an example can, the rule
for [a job of several requests](#a-job-of-several-requests): it stops at a
cancellation or a passed deadline seen between two requests or reported by
a request, and goes on after a fault or a `ResourceLimit`; a forced stop and
the race of completion and cancellation belong to krepi. The documentation
of `execute` holds these functions as a tested example:

```rust
use kalyx::command::serialize;
use kalyx::context::{CancelFlag, Clock, MonotonicClock};
use kalyx::{Context, ErrorKind, Limits, Outcome, Request, execute};

/// The terminal states of a job.
#[derive(Debug, PartialEq, Eq)]
enum JobState {
    Completed,
    Failed,
    Cancelled,
    ResourceExhausted,
}

/// The line that the job publishes for `outcome`, if any, and the errors
/// of its request: the error of the outcome, and the error of `serialize`
/// when the line fails under `context`, the context of the request.
fn publish(outcome: &Outcome, context: &mut Context) -> (Option<Vec<u8>>, Vec<ErrorKind>) {
    let mut errors = Vec::new();
    if let Err(error) = outcome.result() {
        errors.push(error.kind());
    }
    let line = match serialize(outcome, context) {
        Ok(line) => Some(line),
        Err(error) => {
            errors.push(error.kind());
            match outcome.result() {
                // The fallback step, for an error of any kind: a fresh
                // flag and no deadline.
                Err(_) => {
                    let mut fresh = Context::new(Limits::new(), CancelFlag::new());
                    serialize(outcome, &mut fresh).ok()
                }
                // A value or a state is never written again.
                Ok(_) => None,
            }
        }
    };
    (line, errors)
}

/// Runs `requests` one after another on `clock`, the clock of the job,
/// until `deadline`, a reading of that clock, or until `flag` is set, and
/// returns the lines that the job publishes and its terminal state.
fn run_job(
    requests: &[Request],
    mut clock: MonotonicClock,
    deadline: u64,
    flag: &CancelFlag,
) -> (Vec<Vec<u8>>, JobState) {
    let mut lines = Vec::new();
    let mut failed = false;
    for request in requests {
        // Between two requests, the host checks cancellation, then the
        // deadline of the job, itself.
        if flag.is_cancelled() {
            return (lines, JobState::Cancelled);
        }
        if clock.now() >= deadline {
            return (lines, JobState::ResourceExhausted);
        }
        // One context per request: its budget, a copy of the clock of the
        // job, which keeps its origin, the deadline of the job and the
        // flag of the job.
        let mut context =
            Context::with_observers(Limits::new(), Box::new(clock), Box::new(flag.clone()))
                .with_deadline(deadline);
        let outcome = execute(request, &mut context);
        let (line, errors) = publish(&outcome, &mut context);
        lines.extend(line);
        let cancelled = errors.contains(&ErrorKind::Cancelled);
        if cancelled || errors.contains(&ErrorKind::DeadlineExceeded) {
            // The job stops; once its cancellation is requested, it ends
            // cancelled, whatever stopped it.
            let state = if cancelled || flag.is_cancelled() {
                JobState::Cancelled
            } else {
                JobState::ResourceExhausted
            };
            return (lines, state);
        }
        // A fault or a `ResourceLimit` fails the job and does not stop it.
        failed |= !errors.is_empty();
    }
    let state = if failed { JobState::Failed } else { JobState::Completed };
    (lines, state)
}
```

### Table 1: outcomes and the terminal states of a job

krepi's job service is planned with the states `queued`, `running` and
`cancel_requested` and the terminal states `completed`, `failed`,
`cancelled` and `resource_exhausted`. The outcome of a request maps to them
as follows; the job publishes the line of the outcome, when it has one, with
its state. "None under the request's context" means that the line fails
under the context of the request; the job then publishes the
[fallback line](#the-fallback-line) of the error.

| Outcome | Line | Terminal state of the job |
| --- | --- | --- |
| `Ok(Settled::Value(term))` | `value` | `completed`, with the line |
| `Ok(Settled::State(state))`, such as `IterationLimit` | `state` | `completed`, with the state attached: the line names it |
| `Err` of kind `Fault(_)`: invalid or unsupported input, a domain error or an internal defect | `error`; none under the request's context when the work or the output that the request has left is less than the line needs | `failed`, with the line |
| `Err` of kind `ResourceLimit` | `error`, with the limit; none under the request's context when the work or the output that the request has left is less than the line needs | `failed`, with the line: the limit is a limit of the request, which a larger value of the named field or parameter lifts, not the resource scope of the job, and it never stops the job |
| `Err` of kind `Cancelled` | none under the request's context | `cancelled`, after `cancel_requested`: the request stopped at the charge point where the probe of its context reported the cancellation |
| `Err` of kind `DeadlineExceeded` | none under the request's context | `resource_exhausted`, as for a job whose time is exhausted; `cancelled` for a job that has entered `cancel_requested`, as [cancellation first](#cancellation-first) states |
| `serialize` fails under the request's context | the fallback line for an `Err`; none for a value or a state | the error of `serialize` is an error of the request, as [a job of several requests](#a-job-of-several-requests) states |

- **No other states.** A request never ends in `queued`, `running` or
  `cancel_requested`, which belong to the job service, and kalyx itself
  never reports `resource_exhausted` except for a passed deadline: that
  state is also the state of a job whose CPU budget is exhausted, and the
  terminal states of the other exhaustions of its resource scope are fixed
  by krepi's Job contract.
- **Cancelled requests in krepi.** krepi's worker, as first planned, runs
  one request at a time on one thread and does not poll the job service
  during a request, so the probe of a request does not report a
  cancellation that arrives in its middle: the worker handles it at the
  next request boundary, or krepi stops the job by force after its grace
  period. There the `Cancelled` row is reached only by the tests of kalyx.
- **Forced stop.** A job that krepi stops by force ends without an outcome.
  A job stopped after `cancel_requested` and its grace period is
  `cancelled`, marked as forced. A job without a cancel request that is
  stopped by force because its deadline passed, after the grace period, or
  because its CPU budget ran out is `resource_exhausted`, marked as forced,
  and one that has entered `cancel_requested` is `cancelled`, as
  [cancellation first](#cancellation-first) states, so that a passed
  deadline gives the same terminal state whether kalyx observes it or krepi
  stops the job.

#### Cancellation first

krepi's Job contract fixes this rule, and this contract cites it: a job
that has entered `cancel_requested` always ends `cancelled`, whether it
stopped at a request boundary, at a `DeadlineExceeded` that kalyx reported,
or by force, in which case it is marked as forced. The deadline decides the
terminal state only of a job without a cancel request. The rule takes
precedence over the `DeadlineExceeded` row of Table 1, and it agrees with
the order of every charge point, which polls cancellation before it
observes the deadline. Whether a cancel request or the report of a stop
comes first is decided by the race rule of krepi's Job contract.

#### A job of several requests

Table 1 maps the outcome of one request, and that mapping stays as it is. A
job that runs several requests, as in the example above, follows this rule:

- **Lines.** The job publishes the line of every request that ran and has
  one, the [fallback line](#the-fallback-line) included, and ends in one
  terminal state.
- **The errors of a request** are the error of its outcome and, when its
  line fails under the request's own context, the error of `serialize`.
- **Stop.** The job stops, and no further request starts, when one of
  these happens:
  - the host sees cancellation between two requests: `cancelled`;
  - the host sees between two requests that the deadline of the job has
    passed: `resource_exhausted`;
  - the errors of a request include `Cancelled`: `cancelled`; otherwise,
    when they include `DeadlineExceeded`: `resource_exhausted`;
  - krepi stops the job by force: the state of the
    [forced stop](#table-1-outcomes-and-the-terminal-states-of-a-job).

  A job that has entered `cancel_requested` when it stops ends `cancelled`,
  as [cancellation first](#cancellation-first) states. The terminal state
  of a stop takes precedence over every earlier fault and `ResourceLimit`.
- **Without a stop** the job is `failed` when the errors of some request
  include a fault or a `ResourceLimit`, and `completed` otherwise, with the
  state lines attached. A `ResourceLimit` never stops the job: it is a
  limit of its request, whose own context and limits the next request does
  not share.
- **Completion and cancellation.** When every request has run, the race of
  completion and a cancel request is decided by krepi's Job contract.

### Table 2: the limits and who enforces them

The nine fields of `Limits` are limits of the request, enforced by the
checkpoints of kalyx through the context; a value beyond one fails with
`ResourceLimit` naming the field. The host enforces what the context does not
bound.

| Limit | Enforced by | Checkpoints in this release |
| --- | --- | --- |
| `max_work` | kalyx | every charge: the steps of the parser, the term core, the polynomials and the display of a term, and every output byte |
| `max_input_bytes` | kalyx | the parser, before it reads the input |
| `max_output_bytes` | kalyx | `charge_output`: every field of a line and every piece of display text |
| `max_depth` | kalyx | the parser at every level of the input, the term core at every node, the expansion at its entry |
| `max_nodes` | kalyx | `check_storage` at scope `Value`: the syntax nodes of the parser, every new term and every polynomial |
| `max_storage_bytes` | kalyx: a logical quantity, computed from bit lengths and names by the formula of each value kind, and not the memory that a value occupies | `check_storage` at scope `Value`: every new term and every polynomial |
| `max_integer_bits` | kalyx | every number that a literal, an operation of the exact numbers or the display of a number gives or reads |
| `max_exponent` | kalyx | every exponent of the input and of the term core, and the degree of every polynomial |
| `max_frames` | kalyx | `enter_frame`; no operation of this release opens a frame |
| Real memory: the heap and the stack of the worker | krepi's resource scope | the allocations of the job; the logical sizes of kalyx bound what a request retains, not the bytes it allocates |
| CPU time | krepi's resource scope | the budget of the job: this CPU budget is the total budget of the job, and its exhaustion ends the job `resource_exhausted`. A host that derives `max_work` from it still gets `failed` for the `ResourceLimit` of a request, by Table 1 |
| The deadline | both: kalyx observes it at its charge points, within the overrun bound; krepi sets the deadline of the job, which the host converts to the clock of the context of every request, checks it between two requests and stops a job by force after its grace period (as `resource_exhausted`, or `cancelled` after a cancel request) | every charge point of the request |
| Cancellation | both: kalyx observes it at the next charge point; krepi checks it between two requests and stops a job by force after its grace period | every charge point of the request |
| The request fields `operation` and `variable` | kalyx and the host: kalyx compares the operation on at most the bytes of its longest name and reads the variable once by the rule of symbol names before charging one unit per byte; the host bounds the size of a request that it accepts | the charge of the variable, after it is read |

### The names of the crate root

`api/root-names.txt` lists the public names of the crate root, one per line
in byte order: the public modules, the context and its limits, the errors
and result states, the shared result types, `parse`, and `Request`,
`Outcome` and `execute`. The test
`the_crate_root_has_exactly_the_listed_public_names` in
`tests/root_names.rs` derives the public names of the crate root from the
source of `src/lib.rs`, every top-level item with the visibility `pub` and
every name that a `pub use` brings in, and fails when they differ from the
list, so a public name is added to the crate root, removed or renamed only
together with the list
([convention 3](../../conventions/public-api.md#3-extensible-enums-and-records)).
The scan rejects a glob re-export, whose names it cannot list. A macro
exported with `#[macro_export]` lands in the crate root from whichever
module defines it, so the test `no_file_under_src_exports_a_macro` reads
every Rust file under `src/` and fails when one of them exports a macro. A
public name that a macro of `src/lib.rs` generates is not seen, and review
keeps such macros out of the crate root.

### The allocation check

A request leaves no memory behind: run 100 times, every case of the answer
vectors returns the live bytes of the process to their baseline after every
run.

- **The check.** `checks/allocation/` is a Rust package of its own, a
  workspace outside the kalyx package that depends on it by path, since the
  package forbids `unsafe` code in every target and a global allocator needs
  it. Its program installs a counting `#[global_allocator]` that forwards to
  the system allocator and counts the bytes of the blocks that it hands out
  and takes back. It embeds `vectors/r02.tsv` when it is built and reads its
  58 cases with the limits of each, and builds their requests; the live
  bytes after that are the baseline. Each of 100 runs of each case creates a
  context with the limits of the case, executes the request, publishes the
  line of its outcome as a host does, by the
  [fallback step](#the-fallback-line) for an error whose line does not fit
  the context of its request, and drops them. Every run must leave the live
  bytes at the baseline, 0 bytes above it, end with the result kind of its
  case and publish a line, the same line as the first run of its case. The
  program prints nothing before the last run, since the first print keeps a
  buffer for the rest of the process, and exits with 1 when a run fails.
- **The resource profile.** Run with `profile`, the same program measures
  the heap peak and the native stack of every case and of deep inputs at
  several values of `max_depth`, the stack in child processes without
  `unsafe` code; the [resource profile](../../resource-profile.md) records
  the figures, the host and the method. The profile is run by hand and is
  not a step of `cargo xtask check`.
- **`unsafe` code.** The allocator wrapper, an `unsafe impl GlobalAlloc` with
  two unsafe blocks that call the system allocator, is the only `unsafe` code
  of the crate. Its manifest denies `unsafe` code and undocumented unsafe
  blocks; the wrapper allows the first with its reason, and each unsafe
  block and the implementation state why they are sound.
- **How it runs.** The step `kalyx-allocation` of `cargo xtask check`
  format-checks the crate, lints it with Clippy with warnings as errors,
  runs its tests and then runs it, each with its lock file. The tests show
  that the verdict rejects a run that leaves bytes behind, also when every
  run leaves the same amount, a run with another result kind than its case,
  a run without a line and a run whose line differs from the first, and
  that the program reads the 58 cases with their limits. The guard does not scan the
  crate, which is not code of the package, but scans every other file under
  `checks/`; it checks that the lock file of the crate holds only the
  package, the check crate and the packages of `guard/crates.txt`, and
  reports a crate under `checks/` that is not the check crate, as
  [CONTRIBUTING](../../../CONTRIBUTING.md#guard) states.

## Requirements

The command layer of the earlier implementation had no requirement
identifiers, so the requirements of this component are named after what
they state. Tests are in `tests/command.rs` unless the entry names
`src/command/tests.rs`, `tests/root_names.rs`, `tests/host_fixtures.rs`,
`tests/random_requests.rs`, a documentation test, the allocation check or
`xtask`.

### The request and its outcome

A request carries its operation, variable, input, input version, context
version, settings and settings version; `execute` takes it with the context
and returns an outcome that echoes the three versions and holds a value, a
state or an error, never an exit code.

- **Implemented here.** `Request`, `Outcome` and `execute` in
  `src/command.rs`.
- **Evidence.** `the_outcome_echoes_the_versions_of_its_request`, for a
  value, a fault, an unknown operation and a cancelled request, with the
  versions 0 and `u64::MAX`.

### The dispatch table

`eval`, `expand` and `diff` are found by name in one table and do what
[the dispatch table](#the-dispatch-table) states; an unknown operation fails
with `Unsupported` before any work.

- **Implemented here.** `src/command/dispatch.rs`.
- **Evidence.** Positive: `eval_gives_the_exact_number_of_the_input`,
  `expand_gives_the_polynomial_of_the_input_as_a_term` and
  `diff_gives_the_derivative_by_the_variable`. Negative:
  `an_unknown_operation_is_unsupported_before_any_work`. Also
  `one_context_accumulates_the_work_of_every_step`, which checks that the
  steps of an operation and its line charge one context, and
  `the_dispatch_table_holds_eval_expand_and_diff` in
  `src/command/tests.rs`.

### Settings

Settings other than the default fail with `Unsupported`; the default is
accepted with every settings version.

- **Implemented here.** `Settings` and `check_default` in `src/command.rs`.
- **Evidence.** Negative: `a_settings_record_other_than_its_default_is_unsupported`
  in `src/command/tests.rs`, which runs the check of the entry on a settings
  record with a field, since the settings of this release have none.
  Positive: `the_default_settings_are_the_only_settings_and_are_accepted`,
  and the `compile_fail` documentation test of `Settings`, which shows that
  code outside the library builds no other value.

### A missing operand

An input that is empty or holds only whitespace fails with `Syntax` and the
empty span at its end, for every operation, and no operation without an
operand gives a value.

- **Implemented here.** The operations in `src/command/dispatch.rs`, which
  give every input to `parse`.
- **Evidence.** `a_missing_operand_is_a_syntax_error_at_the_end_of_the_input`
  and `an_operation_without_an_operand_never_falls_back_to_a_result`, the
  defect of the earlier implementation.

### The variable

The variable of `expand` and `diff` follows the rule of symbol names and is
checked before the input; `eval` does not read it.

- **Implemented here.** `ring` and `variable_error` in
  `src/command/dispatch.rs`.
- **Evidence.** `the_variable_of_expand_and_diff_follows_the_rule_of_symbol_names`,
  `names_are_case_sensitive` and
  `the_charge_of_the_variable_fails_as_a_resource_limit`.

### Evaluation reads the canonical term

`eval` gives the number of its input and fails with `UnknownSymbol` for a
term that is not a number.

- **Implemented here.** `eval` in `src/command/dispatch.rs`.
- **Evidence.** Positive: `eval_gives_the_exact_number_of_the_input`.
  Negative: `eval_of_a_term_with_a_symbol_is_an_unknown_symbol`.

### Output lines

Every outcome is written as one line in the format of
[the output lines](../../semantics.md#output-lines).

- **Implemented here.** `src/command/line.rs`.
- **Evidence.** `error_lines_carry_the_kind_the_span_and_the_limit` and
  `the_examples_of_the_output_lines_hold`, and in `src/command/tests.rs`
  `a_state_is_written_as_a_state_line`,
  `a_parameter_limit_is_written_with_its_escaped_name`,
  `messages_are_escaped`, `every_kind_has_its_name` and
  `every_limit_field_scope_and_amount_has_its_text`; the shape of every line
  of the property test and of the replay of the vectors; and
  `the_display_of_a_value_is_charged_to_the_context_of_the_line`, which
  checks the work and `max_integer_bits` of the display under the context
  of the line.

### Bounded output

A line charges exactly its bytes as output; one that does not fit
`max_output_bytes` fails with `ResourceLimit` naming that field and returns
no bytes.

- **Implemented here.** `serialize` in `src/command/line.rs`.
- **Evidence.** Negative:
  `a_line_over_max_output_bytes_fails_with_a_resource_limit_and_no_output`,
  with the line at its exact length, one byte less, half and nothing, and
  under too little work. Positive: every test that writes a line checks
  that its output equals its length.

### Determinism

The same outcome is written as the same bytes, whatever shares its nodes,
the clock and the deadline, and the same request charges the same work.

- **Implemented here.** `execute` and `serialize`.
- **Evidence.** `the_same_outcome_is_written_as_the_same_bytes`, a property
  test of 1,000 cases from the fixed seed `0x5EED_0000_0000_0201`.

### The deadline and cancellation

The entry observes the deadline and cancellation of its context at its
charge points, and a request after a cancellation does no work.

- **Implemented here.** The charge points of the steps of `execute` and of
  `serialize`.
- **Evidence.** `cancellation_is_observed_at_the_next_charge_point`, at every
  poll of a request and of a line; `a_flag_cancelled_between_two_requests_stops_the_second`;
  `a_request_that_fails_before_its_first_charge_reports_its_own_error`, for
  an unknown operation, a malformed variable, a reserved name as the
  variable and an input over `max_input_bytes` under a cancelled flag; and
  `a_deadline_on_an_injected_clock_ends_the_request`, with a deadline
  that passed before the request, one that passes in the middle of it, one
  that passes before a line, and a far deadline on the monotonic clock.

### The fallback line

`Cancelled` and `DeadlineExceeded` have no line under the context of their
request, and other outcomes have none there when the work or the output
left is less than the line needs; the host writes the line of an `Err`
outcome again under a fresh context and never writes a value or a state
again.

- **Implemented here.** The rule of the host; `serialize` in
  `src/command/line.rs` writes the same bytes under every context.
- **Evidence.** Positive, the fallback line of each kind:
  `cancelled_and_expired_outcomes_have_no_line_under_their_own_context`, for
  `Cancelled` and `DeadlineExceeded`, and
  `an_outcome_has_no_line_under_its_own_context_when_too_little_is_left`,
  for `ResourceLimit` on `max_work` (`expand` of `(x+1)^5` under every
  `max_work` below 400 that it exhausts), for a fault (`eval` of `0*(1/0)`
  under `max_work = 24`) and for a line over `max_output_bytes`; and
  `an_exhausted_max_work_has_its_line_when_the_work_left_is_enough`, the
  98-byte line of `diff` in a variable of 300 letters `a` under
  `max_work = 200`, written under its own context. Negative:
  `a_value_is_never_written_again_under_another_context`.

### A job of several requests

A job publishes the line of every request that ran and ends in one terminal
state by the rule of [a job of several requests](#a-job-of-several-requests).

- **Implemented here.** The rule of the host, which the example `run_job`
  shows.
- **Evidence.** `a_job_of_several_requests_ends_by_the_stop_rule`, with a
  host of the rule on injected clocks: a completed job; a failed job whose
  faults and `ResourceLimit` outcomes do not stop it; a cancellation and a
  passed deadline of the job seen between two requests; a deadline that
  passes in a request after a fault; and a cancel request during that
  request, polled and not polled by its context, which ends the job
  `cancelled`. The documentation test of `execute` runs `run_job`.

### The answer vectors

All 58 cases of `vectors/r02.tsv` run through `execute` under their limits,
set explicitly from the limits column of each case: the 49 answers are
compared by canonical form, and the 9 errors by kind and, for
`ResourceLimit`, by the limit identifier of the field that the limits column
sets; never by display text or work.

- **Implemented here.** The whole component, with the parser, the term core
  and the polynomials.
- **Evidence.** Positive: `every_vector_of_r02_replays_through_the_command_entry`,
  which compares every case with `compare_case` and also checks the line of
  every case and that it fits the limits of the case: written under the
  context of its request, it has the same bytes as under wide limits.
  Negative: `a_corrupted_expectation_fails_the_comparison`, in which
  `compare_case` rejects a case whose answer, error kind or limit field is
  changed.

### Host fixtures

The four cancellation and budget fixtures planned for krepi's calculator
worker have host counterparts, run by a host of the
[rule for a job of several requests](#a-job-of-several-requests) that writes
a line only when `serialize` has returned all of its bytes: the total budget
of a job exceeded, cancellation between two evaluations, a deadline that
expires on an injected clock, and cancellation in the middle of an
evaluation, which never leaves half a line in the output.

- **Implemented here.** The rule of the host, in the test, over `execute`,
  `serialize` and `Context::with_observers`.
- **Evidence.** `fixture_total_budget_exceeded`,
  `fixture_cancellation_between_two_evaluations`, `fixture_deadline_expiry`
  and `fixture_mid_evaluation_cancellation`, in `tests/host_fixtures.rs`.

### No panic on random requests

No request panics, and every outcome is a value, a state or an error of a
kind that a request without a deadline or a cancellation may end with.

- **Implemented here.** `execute` and `serialize`, with the components below
  them.
- **Evidence.** `ten_thousand_random_requests_never_panic` in
  `tests/random_requests.rs`: 10,000 requests from a fixed seed, of which
  4,000 general, 2,000 with exponents near $2^{32}$, $2^{63}$ and the `u64`
  bound, 2,000 under limits with fields at `u64::MAX` and 2,000 with inputs
  nested up to 20,000 levels; a failing request is reported with its index
  and the seed.

### The names of the crate root

The public names of the crate root are those of `api/root-names.txt`.

- **Implemented here.** `src/lib.rs` and `api/root-names.txt`.
- **Evidence.** Positive: `the_crate_root_has_exactly_the_listed_public_names`.
  Negative: `a_public_name_added_without_the_list_changing_fails` and
  `no_file_under_src_exports_a_macro`. Also
  `the_scan_reads_every_form_of_public_item` and
  `the_list_holds_names_in_byte_order`; all in `tests/root_names.rs`.

### No memory left behind

100 runs of each case of the answer vectors leave the live bytes at their
baseline.

- **Implemented here.** The allocation check in `checks/allocation/` and the
  step `kalyx-allocation` of `cargo xtask check`.
- **Evidence.** The run of the allocation check, and its tests
  `equal_runs_without_leftovers_pass`, `a_run_that_leaves_bytes_behind_fails`,
  `a_run_with_another_result_or_without_a_line_fails`,
  `a_run_with_another_line_fails`,
  `the_check_reads_the_58_cases_with_their_limits` and
  `a_run_publishes_the_fallback_line_of_an_error` in
  `checks/allocation/src/main.rs`. In
  `xtask`,
  `the_allocation_step_checks_and_runs_the_allocation_crate` and
  `an_allocation_failure_stops_the_check` in `xtask/src/check.rs`, and
  `the_lock_file_of_a_check_crate_holds_only_listed_packages`,
  `a_check_crate_without_its_lock_file_is_a_finding`,
  `scans_the_rust_files_of_the_package_outside_src` and
  `files_under_checks_outside_the_check_crate_are_scanned` in
  `xtask/src/guard.rs`.

## Defects of the earlier implementation

- **An operation without an operand fell back to simplification.** The
  command layer took the command word of a request line only when
  whitespace followed it
  (`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/command.rs:72-75`)
  and otherwise read the whole line as an expression to simplify
  (`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/command.rs:316`),
  so the line `eval` succeeded with the symbol `eval`. Here an operation
  without an operand fails with `Syntax`, and an unknown operation with
  `Unsupported` (`an_operation_without_an_operand_never_falls_back_to_a_result`).

## Testing obligations

1. **Requirements.** One positive and one negative test per requirement
   where it has both, as each entry above names them.
2. **Rejected requests.** One negative case each for an unknown operation, a
   missing operand and settings other than the default, and one for the
   defect of the earlier implementation. The settings of this release have
   no field, so no request with settings other than the default can be
   built: the negative case runs the check of the entry, which compares the
   whole record with its default, on a record with a field, and the positive
   case and the `compile_fail` documentation test show that the default is
   the only value that callers can build. The first setting brings a
   request-level negative case.
3. **Lines.** One negative case over `max_output_bytes`, and the property
   test of determinism from a fixed seed, with at least 1,000 cases.
4. **Deadline and cancellation.** With an injected clock and an injected
   probe, never the speed of a clock. The fallback line has a positive case
   for `Cancelled`, `DeadlineExceeded`, `ResourceLimit` on `max_work` and a
   fault, and the rule for a job of several requests a case for each way to
   stop and to end without a stop.
5. **Vectors.** Every case of `vectors/r02.tsv`, compared by canonical form or
   by kind and limit, never by text, and one negative case of a corrupted
   expectation.
6. **Names of the crate root.** One positive and one negative case.
7. **Allocation.** 100 runs of every case of `vectors/r02.tsv` under the
   counting allocator.
8. **Host fixtures and random requests.** One test for each of the four
   fixtures planned for krepi's worker, and 10,000 random requests from a fixed seed
   in four categories of fixed counts.
9. **No message text.** No test asserts the message of an error of the
   library; a test that reads the message field of a line compares it with
   the escaped message of the error.

## Extractability

The component is at tier A1 with no upgrade to A3 planned, so the provable
subset of Rust is not required of it. It is written in that style where the
style costs nothing: the lookup and the escaping are index loops, `match`
takes the place of combinators with closures, no function item is passed as a
value and no closure as a callback (R1 to R4), the enumeration of the
operations has the name `CommandOperation`, unique in kalyx, and no public
enumeration is named `Kind`, `State` or `Outcome` (R6); `Outcome` is a
structure. The lines are built with `Vec<u8>`, `String` and the decimal
formatting of `u64`, and the request holds `String` fields, which a proof
target would need models of; no proof target is registered, and none of its
code has been extracted.

## Current deviations

None: the code and the tests follow every rule above. The rule for settings
other than the default has no failing request in this release, as testing
obligation 2 states.
