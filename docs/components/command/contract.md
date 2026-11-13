# Command entry

**Co-signed.** krepi, whose job service runs the command entry, co-signed
this contract twice: for release 0.1 on 2026-11-07, and for the changes of
release 0.2 on 2026-11-11, the operand table of a request, its answer and
the cause frames of its errors, the `answer` and `error-at` lines, and the
rules below that they change. A change to any part of this list is reviewed
as a change of a contract, co-signed by krepi and approved by the owner:

- **The shapes and the order.** The fields of `Request` and `Operand`; the
  accessors of `Outcome`; the classes of a result, a value, a state or an
  error (`Ok(Settled::Value(_))`, `Ok(Settled::State(_))` and `Err(_)`);
  the [order of a request](#the-request-and-its-order).
- **The lines.** The set of the kinds of [output lines](#output-lines), the
  fields of each kind and the form of the location.
- **The job.** The classes of
  [Table 1](#table-1-outcomes-and-the-terminal-states-of-a-job), the
  division of
  [Table 2](#table-2-the-limits-and-who-enforces-them), the rule for
  [a job of several requests](#a-job-of-several-requests) and the
  [fallback step](#the-fallback-line), with its first argument, that no
  message and no `Parameter(name)` holds text of the caller and that
  parameter names come from a fixed list, its conditions (i) and (ii), the
  sources of frame names, the list of nested categories with their names,
  the bound $d$, and $B \le$ 65,536; the current values of the quantities
  of $B$ are not in the list.
- **The answer vectors.** The results of the 58 lines of `vectors/r02.tsv`
  and their fields within [the promise](#the-answer-vectors-across-releases).
- **The common rules of a line.** One line for each request; fields
  separated by a tab and the line ended by a line feed; the escaping;
  versions in decimal; no partial line; the output charged for a line is
  its length; the same outcome gives the same bytes under every context,
  which the fallback step needs. The estimate of the size of a line before
  it is written does not change these rules.
- **The names of the entry and the host.** The signatures of
  `execute(&Request, &mut Context) -> Outcome` and
  `serialize(&Outcome, &mut Context) -> Result<Vec<u8>>`, and that the
  library never creates a context; the accessors of `Outcome`
  (`input_version()`, `context_version()`, `settings_version()`,
  `result()` and `into_result()`) and `Error::kind()`; and that none of
  the public names that a host uses is removed, renamed or given another
  signature: `Request::new`, `with_input_version`, `with_context_version`
  and `with_settings_version`, `execute`, `kalyx::command::serialize`,
  `Context::new`, `with_observers`, `with_deadline` and `with_timeout`,
  `Limits` and its setters, `CancelFlag`, `MonotonicClock`, `Clock` and
  `CancelProbe`. The functions `publish` and `run_job` of the documentation
  of `execute`, which [the deadline and cancellation](#the-deadline-and-cancellation)
  shows as well, keep their text and pass as a documentation test; they
  use most of these names, which is the mechanical evidence that the names
  still compile.
- **[Determinism](#determinism)**, with its rule for the order of the
  operand table.
- **`vectors/r02.tsv`**: its path, its seven columns, `id`, `operation`,
  `variable`, `input`, `result`, `answer` and `limits`, and the content of
  its 58 cases.
- **The deadline and cancellation.** At every charge point, cancellation is
  polled first, then the deadline, then the work, which
  [cancellation first](#cancellation-first) relies on; the work charged
  after a deadline passes is at most $\max(4032, L)$ units and one running
  primitive operation, with $L$ as the
  [context](../context/contract.md#reading-the-clock) defines it; the
  requests that fail before their first charge point, as
  [the deadline and cancellation](#the-deadline-and-cancellation) lists
  them; the meaning of `Context::new`, `with_observers`, `with_deadline`
  and `with_timeout`, and that the copies of a `MonotonicClock` share its
  origin; and the nine fields of `Limits` with the defaults of
  `Limits::new()`: `max_work` 100,000, `max_input_bytes` 65,536,
  `max_output_bytes` 65,536, `max_depth` 128, `max_nodes` 8,192,
  `max_storage_bytes` 262,144, `max_integer_bits` 4,096, `max_exponent`
  4,096 and `max_frames` 32.
- **The kinds.** The variants of `ErrorKind` outside `Fault`, the variants
  of `Settled`, and that the `class()` of a new `FaultKind` is only `Input`
  or `Internal`.

After the release `v0.3.0`, a change to any part of this list, in any
release, is co-signed before the tag that krepi locks is made, and a change
of release 0.3 before `v0.3.0` is co-signed before `v0.3.0` is made. kalyx
does not know which tag krepi will lock, so the rule applies to the first
tag that holds the change.

**Changes without co-signature.** These changes need no co-signature of
krepi, under the constraints that follow them. The review of a change of a
contract is the closer review that a change of a public interface at a
boundary of the library gets, such as a change of this contract, of the
error kinds, of the charges of the context or of the parser; the review of
an ordinary change is the review of a tested change that leaves those
interfaces as they are, a new row of the operation index aside:

- With the review of an ordinary change, without the owner's approval: a
  new operation, which adds a row to the
  [operation index](#the-dispatch-table) and a section to the contract of
  its component; a change of the signature or the result of an operation
  that no tag has released yet; and a new value kind with its variant of
  `Answer`. A change of the signature or the result of `eval`, `expand` or
  `diff` is not among them.
- With the review of a change of a contract: a new start symbol or a new
  spelling of the parser, and a new `FaultKind` whose `class()` is `Input`
  or `Internal`, which falls into the existing classes of Table 1.
- A checkpoint that a later operation adds is a charge point or comes after
  the first charge point of its request, as
  [Table 2](#table-2-the-limits-and-who-enforces-them) states.
- While the conditions of the [fallback step](#the-fallback-line) hold, no
  text of the caller in a message or a `Parameter(name)`, parameter names
  from the fixed list, conditions (i) and (ii), the sources of frame names
  and $B \le$ 65,536, a longer message, a new and longer name of an error
  kind, a new name in the list of parameter names, and the new current
  values of $K$, $Q$ and $M$ in this contract are reviewed as the change
  that they belong to and are not co-signed. The list of nested categories,
  with their names, and $d$ are fixed: a new nested category or another
  $d$ changes the fallback step and is co-signed. A later operation of a
  listed category adds its examples, as the fallback step states, and adds
  no category.

The constraints, in which the bytes of a line leave out the message field
of an error line, since the wording of a message is not part of the
interface:

- None of these changes changes the results of the 58 lines of
  `vectors/r02.tsv` or their fields within
  [the promise](#the-answer-vectors-across-releases): a new `FaultKind`
  could change the kind field of an error line, and a new spelling the
  reading of an input.
- None changes the result or the line bytes of an input that a released
  version accepts, a request that ends in a value or a state.
- A change with the review of an ordinary change also keeps the result and
  the line bytes of every released request, a request whose operation name
  a released version has. A request that a released version fails with
  `Unsupported` for its unknown operation is not a released request, and
  may get a value or another error once the operation is added: the
  operation `simplify` with the variable `x` and the input `1` fails with
  `Unsupported` in `v0.1.0`. The message of an unknown operation lists the
  operations of its release and changes with the dispatch table.
  `vectors/r02.tsv` holds no such request.

A change that changes any of them is co-signed. An input that a released
version fails, and that a new spelling of the grammar gives a value or
another error, is not either: the grammar only grows.

This contract states the command entry of kalyx: the request that a caller
gives it, with its operand table, and the order in which its parts are
checked; the one dispatch table of the operations, with the index of their
signatures and results; the outcome that it returns, with its answer and
the cause frames of its errors; and the line bytes that it writes for an
outcome, the only output format of the library; how a request is charged
and bounded, its deadline and cancellation, and how its outcome maps to the
states of a job of krepi, the casξ operating system; the list of the
public names of the crate root and the allocation check. It applies to the
module `src/command.rs` with its submodules in `src/command/`, to
`api/root-names.txt` and to the allocation check in `checks/allocation/`.
What each operation reads, its steps, its result and the order of its
errors are stated in the contract of its component, which the
[operation index](#the-dispatch-table) links. The
[architecture](../../architecture.md#requests-and-results) places the
component among the components of release 0.1 and states the rules of its
requests and results, and the
[public API conventions](../../conventions/public-api.md) state the rules
that every public interface follows. The limits, the charges, the deadline
and cancellation belong to the [context](../context/contract.md), the
errors, their cause frames and result states to the
[errors and result states](../errors/contract.md), the input syntax to the
[parser](../syntax/contract.md), the terms and the evaluation of `eval` to
the [term core](../terms/contract.md) and the expansion and
differentiation of `expand` and `diff` to the
[polynomials](../polynomials/contract.md). The bytes of the output lines
and the table of value kinds are stated in
[the input syntax and semantics](../../semantics.md#output-lines).

**Status.** Implemented in `src/command.rs` and `src/command/`, at tier A1
(tested with a written contract). The command entry is written anew for kalyx
after the design rules of the architecture: no code and no test is taken
over from the earlier implementation, which served as a reference, so
[PORTING](../../../PORTING.md) has no row for it. Its first callers are the
command-line program, `src/main.rs`, and the calculator job of krepi,
built from a pinned commit of the library. The operations of this release
read no role of the operand table, so every entry of a table is an unknown
role, and no answer of this release is written as an `answer` line; the
signatures with roles, the check of required and repeated roles, the byte
sum of the operands, the `answer` line and the nested frames are reached by
the unit tests of `src/command/tests.rs`.

## Scope

- **Included.** The request, with its operation, variable, input, operand
  table, versions and settings; the entry `execute` and the order of the
  checks of a request; the dispatch table with `eval`, `expand` and `diff`,
  their signatures and the operation index; the outcome, which echoes the
  versions of its request and holds its answer, state or error, with the
  entry frame of an error; `serialize`, which writes an outcome as one line
  of one of five kinds; the mapping of outcomes to the terminal states of a
  job, the rule for a job of several requests and the fallback step for the
  line of a failed request, with the list of nested categories and the bound
  of the fallback line, and the division of the limits between kalyx and
  the host; the list of the public names of the crate root with its test;
  and the allocation check of repeated requests.
- **Excluded, with their owners.**
  - What `eval` reads, its steps and its result: the
    [term core](../terms/contract.md#evaluation-of-a-request); and those of
    `expand` and `diff`: the
    [polynomials](../polynomials/contract.md#expansion-and-differentiation-of-a-request).
  - Arguments, standard streams, line mode and process exit codes: the
    command-line program, `src/main.rs`, which builds requests,
    calls `execute` and `serialize` and chooses its exit code
    ([the command-line program](../../semantics.md#the-command-line-program)).
    It builds no operand table in this release.
  - The operations beyond the three of this release, with the roles of their
    signatures and the start symbols that read them, and the nested
    categories that they enter: the releases that add them.
  - Sessions, bindings, a context version that is checked against a
    session, the fault `StaleEnvironment` and nested commands: the session
    and command layer, release 0.3.
  - Streaming entries with a progress receiver
    ([convention 13](../../conventions/public-api.md#13-request-inputs-and-progress)):
    with their first streaming operation.
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
re-exports `Request`, `Outcome` and `execute`. `Operand`, `Answer`,
`Settings` and `serialize` are reached through `kalyx::command` and are not
in the crate root. `CauseFrame`, the record of a cause frame, belongs to the
[errors](../errors/contract.md), whose public items the crate root
re-exports.

- `Request`, a `#[non_exhaustive]` record with `Clone`, `Debug`, `PartialEq`
  and `Eq` and these public fields, built by
  `Request::new(operation, variable, input)` with an empty operand table,
  the versions 0 and the default settings, and changed with
  `with_operand(role, text)`, which appends an entry to the table,
  `with_input_version`, `with_context_version`, `with_settings` and
  `with_settings_version`, each `#[must_use]`:

  | Field | Type | Meaning |
  | --- | --- | --- |
  | `operation` | `String` | the name of the operation, looked up in the dispatch table |
  | `variable` | `String` | the variable of `expand` and `diff`; `eval` does not read it |
  | `input` | `String` | the input text, the operand of index 0, in the [input syntax](../../semantics.md) |
  | `operands` | `Vec<Operand>` | the operand table: the entry `operands[k-1]` is the operand of index $k \ge 1$ |
  | `input_version` | `u64` | the version of the input, such as the revision of a cell; echoed |
  | `context_version` | `u64` | the version of the computation context of the input, such as a document or a session; echoed and not checked in this release |
  | `settings` | `Settings` | the settings of the request |
  | `settings_version` | `u64` | the version of the settings, such as their revision in a document; echoed |

- `Operand`, a `#[non_exhaustive]` record with `Clone`, `Debug`,
  `PartialEq` and `Eq`, as `Request` has, and no `Default`, with the public
  fields `role: String` and `text: String`, built by
  `Operand::new(role: &str, text: &str)`. Code outside the library cannot
  write `Request { .. }` or `Operand { .. }`; the `compile_fail`
  documentation tests of both check this (`E0639`).
- `Settings`, a `#[non_exhaustive]` record with no field in this release, with
  `Settings::new()`, `Default`, `Clone`, `Debug`, `PartialEq` and `Eq`. Code
  outside the library cannot write `Settings {}`, so the default is its only
  value; the `compile_fail` documentation test of `Settings` checks this
  (`E0639`).
- `Answer`, a `#[non_exhaustive]` enum with `Clone` and `Debug` and one
  variant for each kind of value that an operation returns: `Answer::Term`
  of a `Term`, the only variant of this release.
- `Outcome`, with private fields, built only by `execute`, with the accessors
  `input_version()`, `context_version()`, `settings_version()`, `result()`,
  which returns `&Result<Settled<Answer>>`, and `into_result()`; `Clone`
  and `Debug`, and `#[must_use]`.
- `execute(request: &Request, context: &mut Context) -> Outcome`.
- `serialize(outcome: &Outcome, context: &mut Context) -> Result<Vec<u8>>`.

`execute` returns an `Outcome` and not a `Result`, so that the versions of a
request come back with every result and every error; the outcome holds the
`Result<Settled<Answer>>` of
[convention 2](../../conventions/public-api.md#2-errors-separate-from-result-states).
Both functions take the context last
([convention 1](../../conventions/public-api.md#1-request-context-last)), and
neither creates one. The component uses public interfaces of the other
components, `parse`, `PolynomialRing` over `Rationals`, the accessors and
`display` of `Term`, `charge` and `charge_output` of the context, and the
accessors of `Error` and `LimitExceeded`, and three crate-internal ones:
`CauseFrame::new` and `Error::with_outer_frame` of the errors, which build
and add the entry frame of an error, and the check of the context for an
amount that may not fit in a `u64`, which checks the byte sum of the
operands.

## Rules

### The request and its order

A request names its operands by index: 0 is `input`, and an index
$k \ge 1$ is the entry `operands[k-1]` of the operand table. Each operation
declares its signature in the contract of its component: the roles of the
table that it reads, whether each is required, optional with a stated
default or repeatable, and the start symbol of the input syntax that reads
it. `operation` and `variable` stay typed fields. `execute` checks a
request in this fixed order and stops at the first failure, which the
outcome holds:

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
3. **The operand table**, entry by entry in the order of the table: each
   entry first charges one work unit, then its role is looked up in the
   signature. A role that the signature does not read fails with
   `Fault(Unsupported)`, and a second entry of a role that is not
   repeatable with `Fault(Syntax)`; both have no span, and their location
   is the index of the entry, written in an `error-at` line.
4. **The required roles** of the table in the signature, not `input`, one
   by one in the order of the signature: each first charges one work unit,
   then the table must hold it. A required role that the table does not
   hold fails with `Fault(Syntax)`, without a span and without a location,
   and its message names the role of the signature. The three operations of
   this release have no role of the table, so this step charges nothing for
   them. An empty `input` is not checked here: the parser reports it in
   step 7, as in release 0.1, with the empty span at the end of the input.
5. **The variable**, for an operation that reads it, as in release 0.1:
   first checked by the rule of symbol names, which charges nothing, then
   charged by the ring.
6. **The byte sum.** When the operand table is not empty, the entry checks
   the byte sum of every text operand, `input` and each entry of the table,
   against `max_input_bytes`. The check is not a charge point. A sum beyond
   the limit fails with `ResourceLimit` naming `Field(max_input_bytes)`,
   with the span `-`, without a location and with the amount
   `Required(sum)`. The sum is added with checked addition, not saturating
   addition: a sum beyond `u64::MAX` is reported as `Bound(u64::MAX)` and
   fails under every value of `max_input_bytes`, `u64::MAX` included, as the
   context reports every amount beyond a `u64`. With an empty table the
   entry does not take this step: the parser checks `input` before it reads
   it, as in release 0.1, with an error that is field for field that of
   release 0.1, the span of the whole source and `Required(length)`, at the
   same time, so `expand` and `diff` charge their ring before the bytes of
   the input are checked.
7. **The operands** are read in the order of the signature, and an error
   carries the index of its operand.
8. **The operation itself.**

An operation without an operand never falls back to another operation, and
an entry of a role that the signature does not read is always an unknown
role. A request with an empty operand table whose signature has no
required role of the table, every case of `vectors/r02.tsv` and every
request of the three operations of release 0.1 among them, takes the steps
of release 0.1 in their order with their charges. Whether the whole work of
such a request is that of release 0.1 once the parser looks up a table of
calls is not part of this rule: work is not compared across releases, and
the replay of the answer vectors does not compare it.

The settings, the operation and the variable are request fields, not text of
an operand, so their errors have no span. The entry reads the operation name
at most up to the length of the longest name of the table, and a role at
most up to the length of the longest role of the signature, so both checks
are bounded whatever the length of the name.

### A missing operand

- **Empty input.** An input that is empty or holds only whitespace has no
  operand. It fails with `Fault(Syntax)` and the empty span at the end of
  the input, for every operation: `parse` finds the end of the input where
  an operand starts. For `expand` and `diff`, a variable that fails comes
  first.
- **A required role.** A required role of the table that the table does not
  hold fails at step 4, with `Fault(Syntax)`, without a span and without a
  location.
- **Other cases.** An operand that is incomplete, such as `1 +`, `()` or
  `(1`, fails with `Fault(Syntax)` by the rules of the parser, with the span
  of the token where an operand is missing or the empty span at the end. An
  empty operation name is an unknown operation, and an empty variable of
  `expand` or `diff` fails as a malformed variable; `eval` does not read the
  variable, so an empty one changes nothing.
- **No fallback.** The operation and its operands are separate fields of the
  request, so an operation without an operand never becomes an operand
  itself, a missing operand never falls back to another operation, and an
  unknown operation never falls back to another operation. This corrects a
  [defect](#defects-of-the-earlier-implementation) of the earlier
  implementation.

### The dispatch table

The table names each operation once, by its name, and a `match` on the
operation that the name gives runs it. An operation is registered only by
its name in this one table: no other place of the library names the
operations, and no request reaches an operation that the table does not
hold. The operation index below has one row for each operation of the
table, in its order: the name, the contract of its component, its
signature, which gives its roles and so its number of operands, the
variant of `Answer` that it returns and the version in which it first
appears. What the operation reads, its steps, its result and the order of
its errors are stated in the contract that the row links, and the test
`the_dispatch_table_holds_eval_expand_and_diff` in `src/command/tests.rs`
checks that the names of the index are those of the table.

| Operation | Contract | Signature | Result | Since |
| --- | --- | --- | --- | --- |
| `eval` | [term core](../terms/contract.md#evaluation-of-a-request) | roles of the table: none; `input`, required, read with the start symbol `input` | `Answer::Term` | `v0.1.0` |
| `expand` | [polynomials](../polynomials/contract.md#expansion-and-differentiation-of-a-request) | roles of the table: none; `input`, required, read with the start symbol `input`; the typed field `variable` | `Answer::Term` | `v0.1.0` |
| `diff` | [polynomials](../polynomials/contract.md#expansion-and-differentiation-of-a-request) | roles of the table: none; `input`, required, read with the start symbol `input`; the typed field `variable` | `Answer::Term` | `v0.1.0` |

Every operation of this release returns a value, `Settled::Value` of an
`Answer::Term`; none ends in a state. `execute` does not follow
[convention 17](../../conventions/public-api.md#17-no-implicit-conventions)
for the exponent 0: every operation reads its input with `parse`, so `eval`
of `0^0` is 1 and `expand` of `x^0` is 1, which only the documentation
states, and neither the outcome nor its line names the convention.

### The outcome

- The outcome echoes the input version, the context version and the
  settings version of its request, with every result: a value, a state, a
  fault and a request failure.
- `Outcome` is a structure with private fields, built only by `execute`, and
  the signatures of `execute` and `serialize` and of the three accessors of
  the versions are those of release 0.1. `result()` returns
  `&Result<Settled<Answer>>`, and `into_result()` returns
  `Result<Settled<Answer>>`; release 0.1 returned `Settled<Term>`.
  `Answer` has one variant for each kind of value that an operation
  returns, and `Answer::Term` is the variant of release 0.1, the result of
  every case of `vectors/r02.tsv`.
- It holds a structured result, `Ok(Settled::Value(answer))` or
  `Ok(Settled::State(state))`, or the `Error` that ended the request, with
  its kind, its span into an operand, its cause frames and, for
  `ResourceLimit`, its `LimitExceeded`. It holds no process exit code and no
  text: a program chooses its exit code from the outcome, and text comes
  only from `serialize`.
- `ErrorKind` is that of release 0.1: `ResourceLimit`, `Cancelled`,
  `DeadlineExceeded` and `Fault(FaultKind)`. A fault kind that a later
  release adds is a new variant of `FaultKind`, within `Fault(_)`, whose
  `class()` is `Input`.
- `Error` keeps `kind()`, `message()` and `exceeded()`, and `frames()`
  returns its [cause frames](../errors/contract.md#cause-frames) as
  `&[CauseFrame]`, outer first, each the name of an operation or of a
  nested category and the index of an operand. The name `CauseFrame` keeps
  apart from `kalyx::context::Frame`, the token of `enter_frame`.
  - The command entry adds the first frame, the entry frame: the operation
    of the request and the index of the operand in which the error arose,
    at an entry of the table (step 3), at the reading of an operand
    (step 7), or in the operation itself (step 8), whose errors `eval`,
    `expand` and `diff` give the index 0 of their input. A request failure
    at a charge has the frame of the step that charged, and none at steps 4
    and 5. An error that concerns no operand, of the settings, the
    operation name, a missing role, the byte sum or the variable, has no
    frame, and neither has an error of a library function that is called
    directly.
  - The frames after it are nested frames, whose names and number
    [the fallback line](#the-fallback-line) bounds. No operation of this
    release adds one.
  - Frames are records on the error only: adding one does not go through
    `enter_frame`, charges nothing and does not count against `max_frames`,
    so the work and the line bytes of the requests of release 0.1 are
    those of that release.
  - `span()` keeps its signature and counts bytes of the text of the
    operand that the innermost frame names; with no frame, or with only
    the entry frame of the index 0, that is the input, as in release 0.1, so
    the spans of the requests of release 0.1 are those of that release.
- The context version is echoed and not checked in this release, which has
  no session.

Code that matches only `Ok(_)`, `Err(e)` and `e.kind()` with a wildcard arm
compiles against `v0.1.0` and against this version, and is to compile
against `v0.3.0`; code that names `Term` or `Settled<Term>` as the result
does not compile against this version. krepi's worker names neither:

```rust
match outcome.result() {
    Ok(_) => { /* completed: publish the line */ }
    Err(e) => match e.kind() {
        ErrorKind::Cancelled => { /* cancelled */ }
        ErrorKind::DeadlineExceeded => { /* resource_exhausted */ }
        _ => { /* failed: ResourceLimit and every Fault */ }
    },
}
```

### Output lines

`serialize` writes an outcome as one line of bytes, in the format that
[the output lines](../../semantics.md#output-lines) state. These rules are
common to every line: a line is UTF-8 text, its fields separated by one tab
and the line ended by one line feed; its first field names its kind, and
its kind fixes its number of fields; versions are decimal `u64` numbers; the
escaping of messages and parameter names is that of release 0.1; every byte
is charged as output, so the output charged for a line is its length, and
a failure leaves no partial line; one request has one line; and the same
outcome gives the same bytes under every context. A line has one of five
kinds:

| Kind | Release 0.1 | This release |
| --- | --- | --- |
| `value` | 5 fields: the kind, the three versions and the display text of the term | the same, for `Answer::Term` only |
| `state` | 5 fields: the kind, the three versions and the name of the state | the same |
| `error` | 11 fields: the kind, the three versions, the error kind, the span, the limit, the scope, the allowed value, the amount and the message | the same fields in the same order with the same bytes, for an error without a location or with the location of the index 0 and no nested frame |
| `answer` | none | 8 fields: the kind, the three versions, the kind of the value, its text, its condition and its assumptions, for every kind of value but a term |
| `error-at` | none | 12 fields: `error-at`, then fields 2 to 11 with the meaning and the bytes of those of an `error` line, and the location, for every other error |

The number of fields of a released kind and the bytes of each field do not
change; new information comes as a new kind of line or as a new field at
the end of a line. The fields of an `answer` line, the location of an
`error-at` line and its grammar, and the base of the span are stated with
the bytes of every field in
[the output lines](../../semantics.md#output-lines). `serialize` is the
only output format of the library
([convention 10](../../conventions/public-api.md#10-bounded-output)): the
command-line program writes its results only through it, and results reach
callers as text only through it, never through `Display`.

### Charging and bounded output

- **`execute`** charges the context as its steps charge it: one unit for
  each entry of the operand table and one for each required role of the
  signature, the ring one unit and one per byte of the variable, the
  parser, the term core and the polynomials as their contracts state. It
  charges no output.
- **`serialize`** charges every byte that it writes with `charge_output`,
  which first checks the request's cumulative `max_output_bytes`, then
  charges one work unit per byte. It writes the line field by field: each
  field with the tab before it is charged and then appended, the display
  text of a value charges its own steps, one unit each, and its pieces, and
  the line feed is charged last. So the output charged for a line is exactly
  its length, and every field is a charge point.
- **The estimate.** Before it writes a line, `serialize` estimates its size
  from the fields that it knows, every field but the display text of a
  value, and reserves that much of its buffer, at most the output that the
  request has left. The estimate only reserves: the charges and their
  charge points are those of the fields, so an estimate never makes a line
  that fits fail.
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

### The answer vectors across releases

`vectors/r02.tsv` uses only `eval`, `expand` and `diff`, 31, 21 and 6
cases, and its lines are `value` and `error` lines: 49 values and 9 errors.
The promise of this release for these 58 lines is that their results, the
kinds of their lines, their numbers of fields and every field but the
message are those that `v0.1.0` writes. The messages are not in it: their
wording is not part of the interface, as
[the output lines](../../semantics.md#output-lines) state, and no test
asserts the wording of a message of the library. The evidence is
[the replay of the answer vectors](#cmd-r14), which compares canonical
forms, error kinds and limit fields. Display text and spans are not
compared byte for byte across releases: the display rules of the term core
and the span rules of the parser keep them, with their own tests, and the
grammar only grows, so they read every input of release 0.1 as that
release did. The checks of line bytes compare lines of the same commit: the
replay through the entry compares each line written under the context of
its request with the same line under wide limits, and the replay through the
command line compares its lines with those of the entry, byte for byte.

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

The step is sound because the length of an error line is bounded by
constants of the library, whatever the input and the limits that the caller
sets:

1. **No text of the caller.** An error line holds no display text, and
   neither its message nor the `Parameter(name)` of a `ResourceLimit` holds
   any text that the caller gave: the operation name, the variable, a role
   or the text of an operand. Text is pointed at only by the span and the
   location; an unknown role whose message named the role would make the
   line as long as the role. The messages of the library are fixed texts,
   to which `ResourceLimit` adds only the name of a limit and a missing role
   the name of the role in the signature. A parameter name can come from a
   caller, since `Context::check_parameter(name, allowed, value)` is public,
   and inside the library a parameter limit can also be built directly with
   the crate-internal `LimitExceeded::new` and `Error::resource_limit`. So
   every place of the library that builds a `LimitId::Parameter`, through
   `check_parameter` or directly, takes its name from one fixed list of
   parameter names of the form `[a-z][a-z0-9_]*`, which this section keeps
   and review checks. The list is empty: no code of the library outside its
   tests builds a `LimitId::Parameter` yet, and the parameter limits of a
   host's own calls of `check_parameter` never reach an outcome of kalyx.
2. **A bound $d$ on the nested frames.** $d$ is the most nested frames that
   an error has, the frames after its entry frame and so the number of `>`
   in its location; it is fixed with the list of nested categories below.
   It is not taken from `max_frames`, which the caller sets for the context
   of the request to any `u64`, while the fallback line is written under
   `Limits::new()`. Two conditions make $d$ independent of the input and of
   the limits:
   1. no nested category occurs twice along one chain of an error, so $d$
      is at most the number of nested categories;
   2. nesting in the syntax adds no frame: nesting inside one operand, of
      parentheses, calls and the arguments of connectives, is shown only by
      the span, and a frame is added only where an operation enters a nested
      category through a fixed step of the library.

   A user function of release 0.3 that made nesting follow the input
   recursively would break the first condition, so that the location could
   grow without a bound that a limit controls; that changes the fallback
   step and is co-signed.
3. **Frame names from the library.** The name of a nested frame is the name
   of an operation of the dispatch table when its step is that operation,
   and otherwise a name from the fixed list of category names. A frame name
   is never a binding name, a variable, a role of the request or the name of
   a user function. A category name is never the name of an operation, and
   a later operation never takes a category name. Every frame name has the
   form `[a-z][a-z0-9-]*`, as every operation name has, and the index of a
   frame is written in decimal, as a version is. So a location shows no text
   of the caller. The list of nested categories, with the operations that
   enter them and the names of their frames:

   | Nested category | Entered from | Frame name |
   | --- | --- | --- |
   | A relation decided by `ineq` | `rel-and`, `rel-or`, `rel-not` | `ineq`, the name of the operation |
   | The evaluation at an algebraic number | `alg-at` | `algebraic-evaluation` |
   | The complex embedding of a number field | `field-value` | `complex-embedding` |
   | The test of membership in a set | `contains` | `membership` |

   The operations of these categories are planned for release 0.2; none is
   in the dispatch table of this release. An error in the reading of an
   operand and an error in the value of a binding are not categories: the
   entry frame names their operand by its index, and the span points into
   it, so a category for them would name the same operand twice. With these
   four categories, none of which enters another, $d = 1$.
4. **The bound of a line.** An `error-at` line has at most
   $B = 181 + K + Q + M + 20 + d \cdot (N + 22)$ bytes, and an `error` line
   fewer. 181 is the first field `error-at`, 8 bytes; the three versions, of
   at most 20 digits each, 60; the span, at most $20 + 2 + 20 = 42$; the
   scope, at most 9, `Temporary`; the allowed value, at most 20; the amount,
   at most 30, `Required(`, 20 digits and `)`; and the 11 tabs and the line
   feed, 12. $K$ is the longest name of an error kind; $Q$ the longest
   limit field, the larger of `Field(max_storage_bytes)`, 24 bytes, and
   `Parameter(`, the longest parameter name of the list and `)`; $M$ the
   longest escaped message of the library; and $20 + d \cdot (N + 22)$ the
   location, an index of at most 20 digits, then for each nested frame `>`,
   a frame name of at most $N$ bytes, `#` and an index of at most 20
   digits. Since every message is a fixed text with at most a name of the
   library added, $K$, $Q$ and $M$ are constants of the library. Their
   current values are $K = 18$, `NonIntegerExponent`; $Q = 24$,
   `Field(max_storage_bytes)`, since the list of parameter names is empty;
   $M = 86$, the message of a variable that is not a symbol name; $d = 1$;
   and $N = 20$, `algebraic-evaluation`, the longest frame name. So
   $B = 371$, and $B \le$ 65,536, the default `max_output_bytes`. An error
   line holds no display text and the fallback line charges one work unit
   per byte, so a line of at most $B \le$ 65,536 bytes also fits the default
   `max_work` of 100,000 units, and under a fresh flag without a deadline
   its writing reports neither `Cancelled` nor `DeadlineExceeded`. krepi
   sizes the queue of the standard output of a job to at least one whole
   line by this bound. A later change may lengthen a message, add a longer
   name of an error kind or add a name to the list of parameter names, and
   update the current values here, as long as every condition of the
   fallback step still holds: no text of the caller, the conditions (i) and
   (ii), the sources of frame names and $B \le$ 65,536. The frame names and
   $d$ are fixed with the list of nested categories, and a new category is
   co-signed.
5. **Evidence.** The deepest chain of an error has exactly $d$ nested
   frames; a deeply nested input, such as 1,000 levels of parentheses or
   1,000 levels of conditions under a raised `max_depth`, has at most $d$
   nested frames; the random requests check that every `Err` outcome has a
   line under `Context::new(Limits::new(), CancelFlag::new())` and at most
   $d$ nested frames; and every place of the library that builds a
   `LimitId::Parameter` takes its name from the list, which review checks.
   The operations of the nested categories come with later changes. The
   change that delivers the operation of a category adds the examples of
   that category and adds the operation to the generator of the random
   requests, which would otherwise check nothing for it; until then
   [Current deviations](#current-deviations) lists the missing examples and
   the operations that the generator lacks. The example of 1,000 levels of
   conditions belongs to no category and waits for the grammar of
   conditions, and is listed there as well. These deviations are cleared
   before the tag `v0.3.0` is made, and those that are left then are named
   in the notice of that tag to krepi.

### Determinism

The same request under the same limits charges the same work and gives the
same outcome in every run, on every host, and the same outcome gives the same
line bytes. Neither the outcome nor the line depends on pointer identity,
on whether terms share nodes, on addresses, on hash order or on time; the
numbers of a line are written in decimal, and the display text of a term
depends only on the term
([convention 8](../../conventions/public-api.md#8-determinism)). A result
depends on the order of the operand table only through the indices of the
operands and through the order of the entries of one repeatable role. Only
the outcome of cancellation and of a deadline depends on the injected probe
and clock. The line of a `DeadlineExceeded` outcome depends on the charge
point where the deadline was observed, so byte-identical lines on different
hosts for an outcome of a deadline need an injected clock; requests that are
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
  work. A request that fails before its first charge point returns that
  error and not `Cancelled`, which is why the host checks cancellation
  between two requests itself. Which requests those are depends on the
  request:

  | Request | First charge point | Fails before it with its own error |
  | --- | --- | --- |
  | An empty operand table and a signature without a required role of the table: every case of `vectors/r02.tsv`, every request of the three operations of release 0.1, and an operation that reads `input` and optional roles only | as in release 0.1 | as in release 0.1: settings other than the default, an unknown operation, a malformed or reserved variable, read once by the rule of symbol names before its charge, and an input over `max_input_bytes`, which the parser checks before it reads the input and which is not a charge point; an empty input fails, as in release 0.1, after the parser charges the end of the input, so cancellation comes first |
  | A nonempty operand table | its first entry | only settings other than the default and an unknown operation |
  | An empty operand table and a signature with a required role of the table | the first charge of step 4 | only settings other than the default and an unknown operation |

  An entry of the table charges one unit before its role is looked up, and
  a required role one unit before the table is searched for it, so an
  error of a role and a missing role come after a charge point, and under
  a cancelled flag the request fails with `Cancelled` there: the list of
  requests that fail before their first charge point has no new entry.
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
by its class, as follows; the job publishes the line of the outcome, when it
has one, with its state. "None under the request's context" means that the
line fails under the context of the request; the job then publishes the
[fallback line](#the-fallback-line) of the error.

| Outcome | Line | Terminal state of the job |
| --- | --- | --- |
| `Ok(Settled::Value(answer))`, of any variant of `Answer` | `value` for a term, `answer` for every other kind of value | `completed`, with the line |
| `Ok(Settled::State(state))`, such as `IterationLimit` | `state` | `completed`, with the state attached: the line names it |
| `Err` of kind `Fault(_)`, of any fault kind, those that later releases add included: invalid or unsupported input, a domain error or an internal defect | `error` or `error-at`; none under the request's context when the work or the output that the request has left is less than the line needs | `failed`, with the line |
| `Err` of kind `ResourceLimit` | `error` or `error-at`, with the limit; none under the request's context when the work or the output that the request has left is less than the line needs | `failed`, with the line: the limit is a limit of the request, which a larger value of the named field or parameter lifts, not the resource scope of the job, and it never stops the job |
| `Err` of kind `Cancelled` | none under the request's context | `cancelled`, after `cancel_requested`: the request stopped at the charge point where the probe of its context reported the cancellation |
| `Err` of kind `DeadlineExceeded` | none under the request's context | `resource_exhausted`, as for a job whose time is exhausted; `cancelled` for a job that has entered `cancel_requested`, as [cancellation first](#cancellation-first) states |
| `serialize` fails under the request's context | the fallback line for an `Err`; none for a value or a state | the error of `serialize` is an error of the request, as [a job of several requests](#a-job-of-several-requests) states |

The seven rows are those of release 0.1: the first row takes every answer
where release 0.1 had a term, and the line of a row takes the `answer` and
`error-at` lines. An answer whose completeness is unsolved, such as an
incomplete list of roots, is still `Ok(Settled::Value(_))`, and its job
ends `completed`: the terminal state says whether the request finished,
not whether its answer is complete. A new variant of `Answer` or of
`MathState`, and a new `FaultKind` whose `class()` is `Input` or `Internal`,
fall into an existing row. Table 1 changes, and is co-signed again, exactly
when one of these holds:

- a variant of `ErrorKind` outside `Fault` is added, a kind whose `class()`
  is `Context`;
- a variant of `Settled` is added;
- an existing class maps to another terminal state, such as a resource limit
  that stops the job;
- a new `FaultKind` has a `class()` other than `Input` or `Internal`; the
  [errors](../errors/contract.md) never give a fault the class `Context`.

So an exhaustion meant to end a job `resource_exhausted`, such as an
exhaustion of memory, cannot be added as a `FaultKind`.

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
bound. The checkpoints are named by their kind; the contract of each
component states its own checkpoints, and a later operation that adds
checkpoints of a kind named here does not change the table. A checkpoint
that a later operation adds is a charge point, or comes after the first
charge point of its request: a check that is no charge point and could come
before the first one, as the byte sum of the operands would if it came
before the charges of the table, changes the list of the requests that fail
before their first charge point, which
[the deadline and cancellation](#the-deadline-and-cancellation) states and
which is co-signed.

| Limit | Enforced by | Checkpoints in this release |
| --- | --- | --- |
| `max_work` | kalyx | every charge: each entry of the operand table and each required role of a signature, the steps of the parser, the term core, the polynomials and the display of a term, and every output byte |
| `max_input_bytes` | kalyx | with an empty operand table, the parser, before it reads the input; with a nonempty table, the byte sum of every text operand, the input and each entry, which the entry checks before it reads the first operand and which is not a charge point |
| `max_output_bytes` | kalyx | `charge_output`: every field of a line and every piece of display text |
| `max_depth` | kalyx | every level of nesting: the parser at every level of the input, the term core at every node, the expansion at its entry |
| `max_nodes` | kalyx | `check_storage` at scope `Value`: the syntax nodes of the parser, every new term and every polynomial |
| `max_storage_bytes` | kalyx: a logical quantity, computed from bit lengths and names by the formula of each value kind, and not the memory that a value occupies | `check_storage` at scope `Value`: every new term and every polynomial |
| `max_integer_bits` | kalyx | every number that a literal, an operation of the exact numbers or the display of a number gives or reads |
| `max_exponent` | kalyx | every exponent, degree and order: the exponents of the input and of the term core, and the degree of every polynomial |
| `max_frames` | kalyx | `enter_frame`; no operation of this release opens a frame, and the cause frames of an error are records that do not count |
| Real memory: the heap and the stack of the worker | krepi's resource scope | the allocations of the job; the logical sizes of kalyx bound what a request retains, not the bytes it allocates |
| CPU time | krepi's resource scope | the budget of the job: this CPU budget is the total budget of the job, and its exhaustion ends the job `resource_exhausted`. A host that derives `max_work` from it still gets `failed` for the `ResourceLimit` of a request, by Table 1 |
| The deadline | both: kalyx observes it at its charge points, within the overrun bound; krepi sets the deadline of the job, which the host converts to the clock of the context of every request, checks it between two requests and stops a job by force after its grace period (as `resource_exhausted`, or `cancelled` after a cancel request) | every charge point of the request |
| Cancellation | both: kalyx observes it at the next charge point; krepi checks it between two requests and stops a job by force after its grace period | every charge point of the request |
| The request fields `operation` and `variable` and the operand table | kalyx and the host: kalyx compares the operation on at most the bytes of its longest name, charges one unit for each entry of the table before it compares its role on at most the bytes of the longest role of the signature, charges one unit for each required role of the signature before it looks for it, and reads the variable once by the rule of symbol names before charging one unit per byte; the host bounds the size of a request that it accepts | the charge of each entry and of each required role, and the charge of the variable, after it is read |

The bounds that the operations of release 0.2 bring (planned) fall into
these fields: the order of a derivative or of a series, the degree of
`rootn` and the index of a root into `max_exponent`; the number of operands
and the check of required roles into `max_work`; scopes into
`max_storage_bytes`; and nested operations into `max_frames`, while the
cause frames of an error are records and do not count against it.

### The names of the crate root

`api/root-names.txt` lists the public names of the crate root, one per line
in byte order: the public modules, the context and its limits, the errors
and result states with `CauseFrame`, the shared result types, `parse`, and
`Request`, `Outcome` and `execute`. `Operand`, `Answer`, `Settings` and
`serialize` are reached through `kalyx::command` and are not in the list.
The test
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
vectors and a request with an operand table return the live bytes of the
process to their baseline after every run.

- **The check.** `checks/allocation/` is a Rust package of its own, a
  workspace outside the kalyx package that depends on it by path, since the
  package forbids `unsafe` code in every target and a global allocator needs
  it. Its program installs a counting `#[global_allocator]` that forwards to
  the system allocator and counts the bytes of the blocks that it hands out
  and takes back. It embeds `vectors/r02.tsv` when it is built and reads its
  58 cases with the limits of each, and builds their requests, with one
  more case: `eval` of `1` with the entry of the role `scope` and the text
  `x: real`, a role that `eval` does not read, so that the request fails
  with `Unsupported` with the entry frame of the index 1 and publishes an
  `error-at` line. The live bytes after that are the baseline. Each of 100
  runs of each case creates a context with the limits of the case, executes
  the request, publishes the line of its outcome as a host does, by the
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
  a run without a line and a run whose line differs from the first, that
  the program reads the 58 cases with their limits, and that the case with
  an operand table fails at its entry and publishes its `error-at` line. The guard does not scan the
  crate, which is not code of the package, but scans every other file under
  `checks/`; it checks that the lock file of the crate holds only the
  package, the check crate and the packages of `guard/crates.txt`, and
  reports a crate under `checks/` that is not the check crate, as
  [CONTRIBUTING](../../../CONTRIBUTING.md#guard) states.

## Requirements

The command layer of the earlier implementation had no requirement
identifiers, so the requirements of this component are numbered here,
`CMD-R01` to `CMD-R18`, a prefix that no other component uses; a number is
never changed or reused. Tests are in `tests/command.rs` unless the entry
names `src/command/tests.rs`, `src/error.rs`, `tests/root_names.rs`,
`tests/host_fixtures.rs`, `tests/random_requests.rs`, a documentation
test, the allocation check or `xtask`.

### CMD-R01

**The request and its outcome.** A request carries its operation, variable,
input, operand table, input version, context version, settings and
settings version; `execute` takes it with the context and returns an
outcome that echoes the three versions and holds an answer, a state or an
error, never an exit code.

- **Implemented here.** `Request`, `Operand`, `Answer`, `Outcome` and
  `execute` in `src/command.rs`.
- **Evidence.** `the_outcome_echoes_the_versions_of_its_request`, for a
  value, a fault, an unknown operation and a cancelled request, with the
  versions 0 and `u64::MAX`; the `compile_fail` documentation tests of
  `Request` and `Operand`, which show that code outside the library builds
  them only with their constructors; and the documentation tests of
  `Request::with_operand` and `Answer`.

### CMD-R02

**The order of checks.** A request is checked in
[the order of a request](#the-request-and-its-order): the settings, the
operation, the entries of the operand table, the required roles, the
variable, the byte sum, the operands and the operation itself, and the first
failure ends it. A request with an empty table and a signature without a
required role of the table takes the steps of release 0.1 with their
charges.

- **Implemented here.** `result_of` in `src/command.rs`, `run` and the
  operations in `src/command/dispatch.rs`, and `check_table`,
  `check_input_bytes` and `read` in `src/command/operands.rs`.
- **Evidence.** `operands_are_read_in_the_order_of_the_signature` in
  `src/command/tests.rs`, which also checks the order of the entries, the
  required roles, the byte sum and the reading;
  `an_unknown_role_is_unsupported_at_its_index`, whose table comes before a
  malformed variable; and, for the steps of release 0.1 and their charges,
  `one_context_accumulates_the_work_of_every_step`,
  `the_charge_of_the_variable_fails_as_a_resource_limit` and
  `an_outcome_has_no_line_under_its_own_context_when_too_little_is_left`,
  which fix the work of requests without a table.

### CMD-R03

**The operand table.** Each entry of the table charges one unit and is
looked up in the signature: an unknown role fails with `Unsupported` and a
second entry of a role that is not repeatable with `Syntax`, both at the
index of the entry; with a nonempty table, the byte sum of the text operands
is checked against `max_input_bytes` with checked addition.

- **Implemented here.** `check_table`, `check_input_bytes` and
  `check_byte_sum` in `src/command/operands.rs`.
- **Evidence.** Negative: `an_unknown_role_is_unsupported_at_its_index`,
  for every operation, and in `src/command/tests.rs`
  `a_role_that_cannot_repeat_is_a_syntax_error_at_its_second_index`,
  `the_byte_sum_of_the_operands_is_checked_against_max_input_bytes` and
  `an_overflowing_byte_sum_is_reported_as_the_u64_bound`. Positive: the
  roles of a signature of those tests that the table takes, repeatable ones
  more than once, and the byte sum at the limit.

### CMD-R04

**The dispatch table and the operation index.** `eval`, `expand` and `diff`
are registered by name in one table and do what the contracts of the
[operation index](#the-dispatch-table) state; an unknown operation fails
with `Unsupported` before any work.

- **Implemented here.** `src/command/dispatch.rs`.
- **Evidence.** Positive: `eval_gives_the_exact_number_of_the_input`,
  `expand_gives_the_polynomial_of_the_input_as_a_term` and
  `diff_gives_the_derivative_by_the_variable`. Negative:
  `an_unknown_operation_is_unsupported_before_any_work`. Also
  `one_context_accumulates_the_work_of_every_step`, which checks that the
  steps of an operation and its line charge one context, and
  `the_dispatch_table_holds_eval_expand_and_diff` in `src/command/tests.rs`,
  which checks the table and that the names of the operation index of this
  contract are those of the table.

### CMD-R05

**Settings.** Settings other than the default fail with `Unsupported`; the
default is accepted with every settings version.

- **Implemented here.** `Settings` and `check_default` in `src/command.rs`.
- **Evidence.** Negative: `a_settings_record_other_than_its_default_is_unsupported`
  in `src/command/tests.rs`, which runs the check of the entry on a settings
  record with a field, since the settings of this release have none.
  Positive: `the_default_settings_are_the_only_settings_and_are_accepted`,
  and the `compile_fail` documentation test of `Settings`, which shows that
  code outside the library builds no other value.

### CMD-R06

**A missing operand.** An input that is empty or holds only whitespace fails
with `Syntax` and the empty span at its end, for every operation; a required
role that the table does not hold fails with `Syntax` without a location;
and no operation without an operand gives a value or falls back to another
operation.

- **Implemented here.** The operations in `src/command/dispatch.rs`, which
  give every input to `parse`, and step 4 in `check_table` in
  `src/command/operands.rs`.
- **Evidence.** `a_missing_operand_is_a_syntax_error_at_the_end_of_the_input`
  and `an_operation_without_an_operand_never_falls_back_to_a_result`, one
  case for each operation, the defect of the earlier implementation; and
  `a_missing_required_role_is_a_syntax_error_without_a_location` in
  `src/command/tests.rs`, with a signature of that test.

### CMD-R07

**Output lines.** Every outcome is written as one line of one of the five
kinds, in the format of [the output lines](../../semantics.md#output-lines),
and the table of value kinds has a row for every variant of `Answer`.

- **Implemented here.** `src/command/line.rs`.
- **Evidence.** `error_lines_carry_the_kind_the_span_and_the_limit` and
  `the_examples_of_the_output_lines_hold`, and in `src/command/tests.rs`
  `a_state_is_written_as_a_state_line`,
  `an_answer_line_has_its_eight_fields`,
  `an_error_at_line_has_its_twelve_fields`,
  `the_examples_of_answers_and_locations_hold`,
  `a_parameter_limit_is_written_with_its_escaped_name`,
  `messages_are_escaped`, `every_kind_has_its_name`,
  `every_limit_field_scope_and_amount_has_its_text` and
  `the_table_of_value_kinds_has_a_row_for_every_answer_variant_and_term_shape`;
  the shape of every line of the property test and of the replay of the
  vectors; and `the_display_of_a_value_is_charged_to_the_context_of_the_line`,
  which checks the work and `max_integer_bits` of the display under the
  context of the line.

### CMD-R08

**Bounded output.** A line charges exactly its bytes as output; one that does
not fit `max_output_bytes` or `max_work` fails with `ResourceLimit` naming
that field and returns no bytes.

- **Implemented here.** `serialize` and `answer_line` in
  `src/command/line.rs`.
- **Evidence.** Negative:
  `a_line_over_max_output_bytes_fails_with_a_resource_limit_and_no_output`,
  with a value line, an error line and an `error-at` line at their exact
  length, one byte less, half and nothing, and under too little work; and
  `representative_lines_pass_at_their_exact_limits_and_fail_one_below`, in
  this file and in `src/command/tests.rs`, which writes the line of each
  representative outcome under `max_output_bytes` and `max_work` at exactly
  what it needs and one less, and checks that the retained storage of the
  context does not change. Positive: every test that writes a line checks
  that its output equals its length.

### CMD-R09

**Determinism.** The same outcome is written as the same bytes, whatever
shares its nodes, the clock and the deadline, and the same request charges
the same work; a sum or a product of the same operands in another order has
the same line, and a result depends on the order of the operand table only
through the indices and the order of a repeatable role.

- **Implemented here.** `execute` and `serialize`.
- **Evidence.** `the_same_outcome_is_written_as_the_same_bytes`, a property
  test of 1,000 cases from the fixed seed `0x5EED_0000_0000_0201`, with
  requests with an operand table and sums and products in both orders of
  their operands; and `operands_are_read_in_the_order_of_the_signature` in
  `src/command/tests.rs`.

### CMD-R10

**Cause frames and spans.** An error of an operand carries the entry frame
of the operation and the index of the operand, an error outside the operands
carries none, the span counts bytes of the operand that the innermost frame
names, and an `error-at` line writes the frames as its location.

- **Implemented here.** `at_operand` and `in_operand` in
  `src/command/operands.rs`, the operations in `src/command/dispatch.rs`,
  and the location in `src/command/line.rs`; the frames themselves in the
  [errors](../errors/contract.md#cause-frames).
- **Evidence.** `the_entry_frame_names_the_operation_and_the_operand`;
  `errors_outside_the_operands_have_no_frame`, in this file and in
  `src/command/tests.rs`; in `src/command/tests.rs`
  `every_nested_category_writes_its_frame_in_the_location`, one example of
  each nested category, built in the test, since their operations come with
  later releases; and `causal_frames_are_records_without_charges` in
  `src/error.rs`.

### CMD-R11

**The deadline and cancellation.** The entry observes the deadline and
cancellation of its context at its charge points, a request after a
cancellation does no work, and a line cancelled at any of its charge points
gives no bytes.

- **Implemented here.** The charge points of the steps of `execute` and of
  `serialize`.
- **Evidence.** `cancellation_is_observed_at_the_next_charge_point`, at every
  poll of a request and of a value, an error and an `error-at` line;
  `a_cancellation_at_any_charge_point_writes_a_whole_line_or_nothing` in
  `src/command/tests.rs`, with a fake clock and an injected probe, for the
  five kinds of lines; `representative_lines_cancelled_at_every_charge_point_leave_nothing`,
  in this file and in `src/command/tests.rs`;
  `a_flag_cancelled_between_two_requests_stops_the_second`;
  `a_request_that_fails_before_its_first_charge_reports_its_own_error`, for
  an unknown operation, a malformed variable, a reserved name as the
  variable and an input over `max_input_bytes` under a cancelled flag, and
  with a nonempty operand table for an unknown operation, which still fails
  with `Unsupported`, and for a malformed variable, which gives `Cancelled`
  at the first entry; and `a_deadline_on_an_injected_clock_ends_the_request`,
  with a deadline that passed before the request, one that passes in the
  middle of it, one that passes before a line, and a far deadline on the
  monotonic clock.

### CMD-R12

**The fallback line.** `Cancelled` and `DeadlineExceeded` have no line under
the context of their request, and other outcomes have none there when the
work or the output left is less than the line needs; the host writes the
line of an `Err` outcome again under a fresh context and never writes a value
or a state again; and every error line fits the bound $B$ under the default
limits.

- **Implemented here.** The rule of the host; `serialize` in
  `src/command/line.rs` writes the same bytes under every context, and
  `CATEGORY_NAMES` and `NESTED_FRAMES` in `src/command/dispatch.rs` are the
  category names and $d$.
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
  `a_value_is_never_written_again_under_another_context`. The bound:
  `a_fallback_line_with_d_nested_frames_fits_its_bound` in
  `src/command/tests.rs`, which writes the longest `error-at` lines, with
  $d$ nested frames of the longest frame name, under the default limits,
  checks that they have at most $B$ bytes and that the current values of
  this contract are those of the code; `a_deep_input_has_no_more_than_d_nested_frames`,
  with 1,000 levels of parentheses; `ten_thousand_random_requests_never_panic`,
  which writes the fallback line of every error; and review, which checks
  that no place of the library builds a `LimitId::Parameter` with a name
  outside the list.

### CMD-R13

**A job of several requests.** A job publishes the line of every request
that ran and ends in one terminal state by the rule of
[a job of several requests](#a-job-of-several-requests).

- **Implemented here.** The rule of the host, which the example `run_job`
  shows.
- **Evidence.** `a_job_of_several_requests_ends_by_the_stop_rule`, with a
  host of the rule on injected clocks: a completed job; a failed job whose
  faults and `ResourceLimit` outcomes do not stop it; a cancellation and a
  passed deadline of the job seen between two requests; a deadline that
  passes in a request after a fault; and a cancel request during that
  request, polled and not polled by its context, which ends the job
  `cancelled`. The documentation test of `execute` runs `run_job`.

### CMD-R14

**The answer vectors.** All 58 cases of `vectors/r02.tsv` run through
`execute` under their limits, set explicitly from the limits column of each
case: the 49 answers are compared by canonical form, and the 9 errors by
kind and, for `ResourceLimit`, by the limit identifier of the field that the
limits column sets; never by display text or work.

- **Implemented here.** The whole component, with the parser, the term core
  and the polynomials.
- **Evidence.** Positive: `every_vector_of_r02_replays_through_the_command_entry`,
  which compares every case with `compare_case` and also checks the line of
  every case and that it fits the limits of the case: written under the
  context of its request, it has the same bytes as under wide limits; and
  `every_vector_of_r02_replays_through_line_mode_byte_for_byte` in
  `tests/cli.rs`, whose lines are those of the entry. Negative:
  `a_corrupted_expectation_fails_the_comparison`, in which `compare_case`
  rejects a case whose answer, error kind or limit field is changed.

### CMD-R15

**Host fixtures.** The four cancellation and budget fixtures planned for
krepi's calculator worker have host counterparts, run by a host of the
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

### CMD-R16

**No panic on random requests.** No request panics, every outcome is a
value, a state or an error of a kind that a request without a deadline or a
cancellation may end with, and every error has its fallback line with at most
$d$ nested frames.

- **Implemented here.** `execute` and `serialize`, with the components below
  them.
- **Evidence.** `ten_thousand_random_requests_never_panic` in
  `tests/random_requests.rs`: 10,000 requests from a fixed seed, of which
  4,000 general, some with an operand table, 2,000 with exponents near
  $2^{32}$, $2^{63}$ and the `u64` bound, 2,000 under limits with fields at
  `u64::MAX` and 2,000 with inputs nested up to 20,000 levels; each error is
  also written under `Context::new(Limits::new(), CancelFlag::new())`, and a
  failing request is reported with its index and the seed.

### CMD-R17

**The names of the crate root.** The public names of the crate root are
those of `api/root-names.txt`.

- **Implemented here.** `src/lib.rs` and `api/root-names.txt`.
- **Evidence.** Positive: `the_crate_root_has_exactly_the_listed_public_names`.
  Negative: `a_public_name_added_without_the_list_changing_fails` and
  `no_file_under_src_exports_a_macro`. Also
  `the_scan_reads_every_form_of_public_item`,
  `the_list_holds_names_in_byte_order` and
  `every_public_enum_is_listed_and_non_exhaustive_but_the_exceptions`, which
  checks that `Answer` is listed and `#[non_exhaustive]`; all in
  `tests/root_names.rs`.

### CMD-R18

**No memory left behind.** 100 runs of each case of the answer vectors and
of the request with an operand table leave the live bytes at their
baseline.

- **Implemented here.** The allocation check in `checks/allocation/` and the
  step `kalyx-allocation` of `cargo xtask check`.
- **Evidence.** The run of the allocation check, and its tests
  `equal_runs_without_leftovers_pass`, `a_run_that_leaves_bytes_behind_fails`,
  `a_run_with_another_result_or_without_a_line_fails`,
  `a_run_with_another_line_fails`,
  `the_check_reads_the_58_cases_with_their_limits`,
  `the_check_runs_a_request_with_an_operand_table` and
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
   missing operand, an unknown role, a second entry of a role that is not
   repeatable, a missing required role, a byte sum over `max_input_bytes`
   and settings other than the default, and one for the defect of the
   earlier implementation. The settings of this release have no field, so
   no request with settings other than the default can be built: the
   negative case runs the check of the entry, which compares the whole
   record with its default, on a record with a field, and the positive case
   and the `compile_fail` documentation test show that the default is the
   only value that callers can build. The first setting brings a
   request-level negative case. The operations of this release read no role
   of the table, so the cases of repeated and missing roles and of the byte
   sum run the steps of the entry with signatures of the unit tests, which
   the dispatch table does not hold; the first operation with roles of the
   table brings their request-level cases.
3. **Lines.** One negative case over `max_output_bytes`, the property test
   of determinism from a fixed seed, with at least 1,000 cases, and for each
   kind of line a case of its fields.
4. **Deadline and cancellation.** With an injected clock and an injected
   probe, never the speed of a clock: a cancellation at every charge point
   of a request and of each kind of line. The fallback line has a positive
   case for `Cancelled`, `DeadlineExceeded`, `ResourceLimit` on `max_work`
   and a fault, and the rule for a job of several requests a case for each
   way to stop and to end without a stop.
5. **Vectors.** Every case of `vectors/r02.tsv`, compared by canonical form or
   by kind and limit, never by text, and one negative case of a corrupted
   expectation.
6. **Names of the crate root.** One positive and one negative case.
7. **Allocation.** 100 runs of every case of `vectors/r02.tsv` and of the
   request with an operand table under the counting allocator.
8. **Host fixtures and random requests.** One test for each of the four
   fixtures planned for krepi's worker, and 10,000 random requests from a
   fixed seed in four categories of fixed counts, each error with its
   fallback line.
9. **No message text.** No test asserts the wording of a message of an
   error of the library. Two tests check what a rule asks of a message:
   that the message of a missing role ends with the name of the role, and
   that the message of a variable that is not a symbol name, the longest
   message of the library, has the $M$ bytes that
   [the fallback line](#the-fallback-line) states. A test that reads the
   message field of a line compares it with the escaped message of the
   error.

## Extractability

The component is at tier A1 with no upgrade to A3 planned, so the provable
subset of Rust is not required of it. It is written in that style where the
style costs nothing: the lookup of an operation and of a role, the checks of
the operand table, the byte sum, the reading of the operands, the location
and the escaping are index loops, `match` takes the place of combinators
with closures, no function item is passed as a value and no closure as a
callback (R1 to R4), the enumeration of the operations has the name
`CommandOperation`, unique in kalyx, and no public enumeration is named
`Kind`, `State` or `Outcome` (R6); `Outcome` is a structure. The lines are
built with `Vec<u8>`, `String` and the decimal formatting of `u64`, and the
request holds `String` fields and a `Vec<Operand>`, which a proof target
would need models of; no proof target is registered, and none of its code
has been extracted.

## Current deviations

The evidence of the [fallback line](#the-fallback-line) for the nested
categories and for deep conditions needs operations and a grammar that
later changes deliver, so these twelve parts of it are missing from the
tests. The change that delivers the operation or the grammar adds the part
and removes its item here; the items are cleared before the tag `v0.3.0` is
made, and those that are left then are named in the notice of that tag to
krepi.

1. **The deepest chain.** An error of a request with exactly $d$ nested
   frames: with the first operation that enters a nested category, `alg-at`.
2. **A relation decided by `ineq`.** A request of `rel-and` whose left
   relation fails in `ineq`, with the location `0>ineq#0`: with `rel-and`
   and `ineq`.
3. **The evaluation at an algebraic number.** A request of `alg-at` whose
   error has the nested frame `algebraic-evaluation` at the right index:
   with `alg-at`.
4. **The complex embedding.** A request of `field-value` whose error has the
   nested frame `complex-embedding` at the right index: with `field-value`.
5. **The membership test.** A request of `contains` whose error has the
   nested frame `membership` at the right index: with `contains`.
6. **`rel-and` in the random requests.** The generator of
   `tests/random_requests.rs` lacks `rel-and`, so its check of at most $d$
   nested frames covers none of its chains: with `rel-and`.
7. **`rel-or` in the random requests**, as the item before: with `rel-or`.
8. **`rel-not` in the random requests**, as the item before: with `rel-not`.
9. **`alg-at` in the random requests**, as the item before: with `alg-at`.
10. **`field-value` in the random requests**, as the item before: with
    `field-value`.
11. **`contains` in the random requests**, as the item before: with
    `contains`.
12. **Deep conditions.** A request of 1,000 levels of conditions, under a
    raised `max_depth`, with at most $d$ nested frames: with the grammar of
    conditions.
