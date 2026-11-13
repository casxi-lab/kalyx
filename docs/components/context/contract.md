# Context and limits

The paragraph "Co-signed" at the start of the
[contract of the command entry](../command/contract.md#command-entry) states
which parts of this contract krepi has co-signed and when a change to them
needs krepi's co-signature again.

This contract states how a kalyx request is accounted for: the `Limits` of
the request, the `Context` that every stage of the request charges, how a
charge observes cancellation and the deadline, how output is bounded, and
how the costs of open frames and reserved temporaries are kept within the
limits. It applies to the module `src/context.rs` with its submodules
`src/context/limits.rs`, `src/context/storage.rs` and
`src/context/observer.rs`, and to every function of the library that takes a
context. The [architecture](../../architecture.md#context-api) places the
component among the foundations, and the
[public API conventions](../../conventions/public-api.md) state the rules that
every public interface follows; conventions
[1](../../conventions/public-api.md#1-request-context-last),
[4](../../conventions/public-api.md#4-limits-built-from-defaults),
[6](../../conventions/public-api.md#6-no-hidden-caps),
[8](../../conventions/public-api.md#8-determinism),
[9](../../conventions/public-api.md#9-no-global-state) and
[10](../../conventions/public-api.md#10-bounded-output) concern the context
and are not restated here. The errors that the context reports are those of
the [errors and result states](../errors/contract.md).

**Status.** Implemented in `src/context.rs`, at tier A1 (tested with a written
contract). Its first caller in the library is the exact numbers
(`kalyx::number` and `kalyx::coefficient`), which check `max_integer_bits`
and `max_exponent` and charge work; the integer kernel of `kalyx::number`
also checks the cost of every value that it returns with `check_storage` at
scope `Value`. The term core (`kalyx::term`) checks
`max_depth`, `max_integer_bits` and `max_exponent`, checks the cost of every
new term with `check_storage` at scope `Value`, and charges work and output.
The parser (`kalyx::syntax`) checks `max_input_bytes` and `max_depth`, checks
the count of its syntax nodes with `check_storage` at scope `Value`, and
charges work. The polynomials (`kalyx::polynomial`) check `max_depth` and
`max_exponent`, check the cost of every polynomial with `check_storage` at
scope `Value`, and charge work. The command entry (`kalyx::command`) runs
these under the context of its request and charges every byte of the lines
that it writes with `charge_output`; it creates no context. The command-line
program creates one context for each request that it runs.

## Interface

The crate root re-exports `Context` and `Limits`. The module
`kalyx::context` holds them and the rest of the component:

- `Limits`, a `#[non_exhaustive]` record of nine public `u64` fields, with
  `Limits::new()`, `Default`, one `with_<field>` method per field and
  `get(LimitField)`;
- `Context`, with the constructors `Context::new(limits, cancel)`, which uses
  the monotonic clock and the cancellation flag `cancel`, and
  `Context::with_observers(limits, clock, probe)`, which takes any clock and
  probe; the builders `with_deadline(at)` and `with_timeout(nanos)`; the
  readers `limits()`, `work_used()`, `output_used()`, `open_frames()`,
  `frame_cost(&frame)` and `retained()`; the charge points `charge(units)`,
  `charge_output(bytes)`, `enter_frame()` and `set_frame_cost(&frame, cost)`;
  `leave_frame(frame)`, `reserve(cost)` and `release(reserved)`; and the
  checks `check(field, value)`, `check_parameter(name, allowed, value)` and
  `check_storage(cost, scope)`;
- the tokens `Frame` and `Reserved`, with `Reserved::cost()`;
- `Storage { nodes, bytes }`, `#[non_exhaustive]`, with `Storage::new`,
  `Storage::ZERO`, `saturating_add` and `saturating_sub`, and the trait
  `StorageCost`;
- the traits `Clock` and `CancelProbe` and their default implementations
  `MonotonicClock` and `CancelFlag`;
- the constants `POLL_WINDOW` (64) and `LARGE_CHARGE` (64) and the function
  `overrun_bound(last_large)`.

Crate-internal: `charge_at`, `check_at` and `check_storage_at`, which put the
caller's span on the error; `check_bound_at`, which is `check_at` for an
amount that may not fit in a `u64` and rejects such an amount under every
limit with `LimitAmount::Bound(u64::MAX)`; `check_width_at`, which is
`check_bound_at` for a quantity that a machine width bounds as well as a
field, such as an exponent stored as an `i64`: it checks the amount against
the smaller of the field and the width, and an excess names the field with
that effective value as `allowed`, as the
[errors](../errors/contract.md#bounds-set-by-a-machine-width) state, while
`Nodes` and `StorageBytes` keep the exact retained totals of
`check_bound_at`; and the `Observer` adapter that holds the clock and the
probe.

Every charge point and check returns `Result<_>` with the library's `Error`.
A request failure is built only here, through the crate-internal constructors
of the errors component.

## Requirements

The requirement identifiers are those of the earlier implementation of the
casξ computer algebra system; they are never renumbered or reused. CTX-R03
is rewritten here, as its entry states. Each entry states the requirement as
kalyx implements it, where it is implemented and the tests that are its
evidence; all tests named below are in `tests/context.rs` unless the entry
names `src/context/tests.rs`.

### CTX-R01

**Work charges.** A charge succeeds when it observes no cancellation and no
expiry and the work used plus the amount does not exceed `max_work`; the work
used then grows by exactly the amount. A failed charge leaves the work used
unchanged, and the work used never exceeds `max_work`. This holds for every
`u64` amount, including sums that do not fit in a `u64`, which fail with the
amount `LimitAmount::Bound(u64::MAX)`.

- **Implemented here.** `Context::charge`, and the work part of
  `charge_output`, `enter_frame` and `set_frame_cost`: each computes the new
  total with a checked addition, compares it with `max_work` and writes it
  only after every check of the entry has passed.
- **Evidence.** Positive: `ctx_r01_charges_add_exactly_within_max_work`.
  Negative: `ctx_r01_a_failed_charge_changes_no_work`. Also
  `ex1_charges_accumulate_within_the_budget`,
  `ex2_exhausted_budget_is_a_resource_error` and
  `exact_budget_is_accepted_and_overflow_rejected`.

### CTX-R02

**Priority of failures.** A charge polls the cancellation probe first and
fails with `Cancelled` when it reports cancellation. Otherwise, when the
deadline has been observed to pass, it fails with `DeadlineExceeded`.
Otherwise, when the work does not fit: with a deadline set, the clock is read
once more, and a reached deadline fails the charge with `DeadlineExceeded`
and records the expiry; otherwise the charge fails with `ResourceLimit`
naming `max_work`. Only a failed work check reads the clock once more: a
failed check of an entry's own limit (`max_output_bytes`, `max_frames` or
the retained totals) reports that limit without a reading, so an expiry that
the polling step did not observe does not take precedence over it. The order
of the checks within each entry is stated under [charging](#charging). The
error carries the span that the caller of the charge
gave (none through the public entries); its message is not part of the
requirement.

- **Implemented here.** The private `observe` and `exhausted` steps of every
  charge point.
- **Evidence.** Positive:
  `ctx_r02_failures_are_reported_cancellation_then_deadline_then_work`.
  Negative: `ctx_r02_without_an_expiry_exhausted_work_is_a_resource_limit`.
  Also `cancellation_takes_priority_over_an_exhausted_budget`,
  `expired_deadline_takes_priority_over_an_exhausted_budget`,
  `each_entry_checks_its_limits_in_a_fixed_order`, and in
  `src/context/tests.rs` `an_unobserved_expiry_still_precedes_work_exhaustion`,
  `cancellation_precedes_an_expired_deadline` and
  `request_failures_carry_the_span_of_the_caller`.

### CTX-R03

**Clock readings.** Rewritten: a large charge no longer leaves a full window
of charges without a reading behind it. While a deadline is set and no
expiry has been observed, a charge that observes no cancellation reads the
clock when it is the first charge after the deadline was set, when its amount
is zero, when its amount is at least `LARGE_CHARGE` (64 units), before the
work it pays for, when it is the next charge after such a large charge, and
when the 63 counted charges before it made no polling reading. When the work
does not fit, the clock is read once more ([CTX-R02](#ctx-r02)); that reading
leaves the credit unchanged, so it neither starts nor shortens a window. A
charge that observes
cancellation reads no clock, changes nothing and is not counted. Entering a
frame and recording a frame cost poll as charges of one unit, and charging
output polls as a charge of its byte count. After an expiry is observed the
clock is not read again until a deadline is set again. The work charged after
the deadline passes is bounded as [reading the clock](#reading-the-clock)
states. NUM-R10 and COL-R11, which cite this requirement, follow the
rewritten rule when their components arrive.

- **Implemented here.** The private `poll_deadline` step, with a credit of
  `POLL_WINDOW - 1` small charges after a small or zero reading and none
  after a large one.
- **Evidence.** Positive:
  `ctx_r03_the_charge_after_a_large_charge_reads_the_clock`. Negative:
  `ctx_r03_at_most_63_small_charges_pass_without_a_reading`. Also
  `the_clock_is_read_on_a_fixed_schedule`,
  `without_a_deadline_no_clock_is_read`,
  `a_deadline_right_after_a_large_charge_reading_overruns_by_at_most_the_bound`,
  `a_deadline_right_after_a_small_charge_reading_overruns_by_at_most_the_bound`,
  `frame_operations_alone_observe_a_deadline_within_the_bound`, and in
  `src/context/tests.rs` `an_expired_deadline_stops_the_first_charge_and_stays_final`,
  `replacing_the_deadline_reads_the_clock_on_the_next_charge`,
  `small_charges_are_bounded_between_clock_reads`,
  `zero_and_large_charges_read_the_clock_immediately`,
  `every_clock_read_restarts_the_interval`,
  `a_timeout_counts_from_one_reading_of_the_clock` and
  `contexts_without_a_deadline_are_unchanged`.

### CTX-R04

**Cancellation.** Every charge point polls the cancellation probe first. A
cancellation becomes visible to the probe eventually: the default
`CancelFlag` is an atomic flag that its clones share, from any thread, and
nothing is stated about the delay with which a flag set by another thread
becomes visible. Once the cancellation is visible to the probe, the next
charge point polls it and fails with `Cancelled`. A reservation is not a charge point.

- **Implemented here.** The first step of `observe`, at `charge`,
  `charge_output`, `enter_frame` and `set_frame_cost`.
- **Evidence.** Positive:
  `ctx_r04_cancellation_is_observed_at_the_next_charge_point`. Negative:
  `ctx_r04_cancelling_one_flag_does_not_stop_another_request`. Also
  `ex3_cancellation_is_shared_by_clones_of_the_flag`,
  `cancellation_is_shared_but_does_not_cancel_unrelated_requests`,
  `host_cancelled_between_two_evaluations`, and in `src/context/tests.rs`
  `a_selected_poll_reads_the_shared_cancellation_flag`,
  `other_contexts_and_threads_do_not_consume_polls` and
  `simultaneous_probes_keep_independent_poll_counts`.

### CTX-R07

**Integer bits.** An integer of $b$ bits is admitted when $b$ is at most
`max_integer_bits` and otherwise rejected with `ResourceLimit` naming
`max_integer_bits`. The checks of `max_integer_bits` do not follow
[convention 17](../../conventions/public-api.md#17-no-implicit-conventions):
each entry compares a bound of its own on the bits of its result, such as
$\max(\lvert a \rvert, \lvert b \rvert) + 1$ for a sum, which only its
documentation states, and the amount of the error does not name the bound.

- **Implemented here.** `Context::check(LimitField::IntegerBits, b)`. Its
  callers are the operations of `Rational` and the new elements of
  `Rationals`, which check a bound on the bits of their results, as the
  [exact numbers](../numbers/contract.md#checks-and-charges) state, and the
  operations of `Integer` and the functions of the integer kernel, which
  check a bound on entry and the bounds of their steps, as the
  [integer kernel](../numbers/contract.md#the-integer-kernel) states, and
  the constructor and the element operations of `PrimeField`, which check
  bounds computed from the modulus, as the
  [prime fields](../numbers/contract.md#prime-fields) state.
- **Evidence.** Positive: `ctx_r07_an_integer_of_max_integer_bits_is_admitted`.
  Negative: `ctx_r07_one_bit_more_is_a_resource_limit`.

### CTX-R08

**No panics.** The operations of the context return on every input that their
types can represent: no arithmetic overflow, index or allocation size of the
context's own makes them panic. Sums that do not fit in a `u64` are limit
breaches, tokens of closed frames are ignored, and a release never takes the
temporaries below zero.

- **Implemented here.** Every entry of `src/context.rs`: checked additions
  for every total that is compared with a limit, saturating arithmetic only
  where an invariant makes the result exact, indexing only after a bounds
  check. Allocation failure of the frame table is outside this requirement,
  as it is for every allocation of the library.
- **Evidence.** Positive: `ctx_r08_extreme_inputs_return_without_panicking`.
  Negative: `ctx_r08_overflowing_sums_and_stale_tokens_are_reported_not_panics`.
  Both the test and the release profiles keep overflow checks, so an
  overflow in any test would fail it rather than wrap.

### Requirements of the earlier implementation kept elsewhere

- **CTX-R05, nested calculation commands,** is moved out. The command depth
  of the earlier implementation, bounded by the smaller of its parse depth and
  8, becomes a frame of the generic frame accounting below, bounded by
  `max_frames`; nested commands themselves come with the session and command
  layer and with user functions and programs, planned for 0.3.
- **CTX-R06, user-function frames,** is split. Its generic part is the frame
  accounting of this contract. The frame semantics of user functions come
  with user functions and programs, planned for 0.3, which rewrite its
  wording on these rules.
- **CTX-R09, iteration caps are result states,** belongs to the
  [errors and result states](../errors/contract.md#ctx-r09); the result
  states of iterative methods come with the numerical kernel and evaluation
  framework, planned for 0.3.

## Rules

### Limits

`Limits` has nine fields. Each bounds exactly one quantity, has a default and
is applied as it is given: no code bounds a field by a constant, by another
field or by a machine width that no field names.

| Field | Bounds | Default |
| --- | --- | --- |
| `max_work` | work units charged by the request | 100000 |
| `max_input_bytes` | bytes of the request's input; with a nonempty operand table, of all its text operands together | 65536 |
| `max_output_bytes` | bytes of all display and serialization of the request, cumulative | 65536 |
| `max_depth` | nesting depth of syntax, terms and values | 128 |
| `max_nodes` | nodes retained at one time: the costs of the open frames, the reserved temporaries and the value being admitted | 8192 |
| `max_storage_bytes` | logical storage bytes retained at one time, over the same parts as `max_nodes` | 262144 |
| `max_integer_bits` | bits of one integer | 4096 |
| `max_exponent` | absolute value of one integer exponent; also degrees and orders of derivatives | 4096 |
| `max_frames` | frames open at one time | 32 |

The bytes that `max_input_bytes` bounds are those of the input alone, which
the parser checks before it reads it, when the operand table of the request
is empty; with a nonempty table, they are the byte sum of every text
operand, the input and each entry of the table, which the
[command entry](../command/contract.md#the-request-and-its-order) adds with
checked addition and reports as `Bound(u64::MAX)` when it does not fit in a
`u64`. This measure does not follow
[convention 17](../../conventions/public-api.md#17-no-implicit-conventions):
only the documentation of the command entry and of
`LimitField::InputBytes` states it, and the amount of the error does not
name it.

- **The number of fields.** `LimitField` has one variant per field.
  Compile-time assertions in `src/context/limits.rs` fix that its list
  `LimitField::ALL` has as many entries as `Limits` has fields (a pattern
  that names every field without `..`) and that there are at most ten, so
  one field is left for a future limit. A new limit is a new field with a
  default.
- **Derived bounds.** The scale bounds of features are derived from the
  fields, never written as constants, and are reported with the field they
  derive from:
  - degrees, orders and powers from `max_exponent`;
  - the number of terms, collection elements, matrix cells and temporary
    elements from `max_nodes`, at least one node per element: a count is
    checked as `check_storage(Storage::new(count, 0), LimitScope::Value)`,
    or with the cost of its value kind when that kind has a formula, so open
    frames and temporaries count as well, and an excess has the scope
    `Value`;
  - the logical bytes of a value, a frame cost or a temporary from
    `max_storage_bytes`; the size of one value is a special case of the
    retained total;
  - the bits of a working precision from `max_integer_bits`;
  - nested commands and user calls from `max_frames`.
- **Parameters.** A bound that is none of these is an explicit parameter of
  the request, checked by `check_parameter(name, allowed, value)` and
  reported with `LimitId::Parameter(name)`. A size parameter without
  elements, such as the dimensions of an empty matrix, is such a parameter.
  An iteration cap is a parameter of its method, and reaching it is a result
  state, not a limit.

### Three choices

- **No separate limit on elements.** The number of elements is bounded by
  `max_nodes`, since every element is at least one node.
- **A separate `max_output_bytes`.** Output is a fixed byte format and cannot
  be derived from nodes. Its default is no larger than that of `max_work`, so
  under the default limits output reaches its own limit before the work.
- **A separate `max_storage_bytes`.** It bounds the same retained parts as
  `max_nodes`, measured in logical bytes instead of nodes; each field still
  bounds one quantity. Which of the two is reached first depends on the byte
  formulas of the value kinds, so the formulas are part of the contract. When
  both are exceeded, `Nodes` is reported. Logical bytes are computed from bit
  lengths and are not the memory a value occupies; the host, such as a krepi
  job, bounds real memory.

### Storage costs

- **Interface.** The cost of a retained value is a `Storage { nodes, bytes }`.
  Each value kind has one formula: a value that carries everything the
  formula needs implements `StorageCost`, and a value whose formula needs
  its parent structure takes its cost from a method of the parent, a
  coefficient from `measure` of its coefficient ring and a polynomial from
  `storage` of its polynomial ring. The context takes the computed `Storage`
  and never computes a formula or calls back.
- **Arithmetic.** `Storage::saturating_add` and `saturating_sub` are for the
  formulas and for reported amounts. The totals that the context compares
  with `max_nodes` and `max_storage_bytes` are exact sums with checked
  additions; a sum that does not fit in a `u64` exceeds the limit of its
  component and is reported with the amount `LimitAmount::Bound(u64::MAX)`.
- **Formulas.** Each formula depends only on the value and, for a coefficient
  or a polynomial, its parent structure, never on the platform or the memory
  layout. A rational $n/d$ costs
  $(1, \lvert n \rvert + \lvert d \rvert + 3)$ wherever it occurs, where
  $\lvert x \rvert$ is the bit length of $x$. The formulas of terms and of
  univariate polynomials are fixed by the contracts of the term core and of
  the polynomials, as the
  [architecture](../../architecture.md#storage-bytes) states them; those of
  later value kinds are fixed with them. This component ships no value kind
  and so no implementation of `StorageCost`.
- **Compatibility.** A formula becomes part of the compatibility contract with
  the release tag of its component. Changing one changes which limit is
  reached first, so it is a change of the answer vectors, made on purpose.

### Charging

- The amount of a charge depends only on the operation it pays for, never on
  the limits or on the remaining work.
- Each charge point polls cancellation, then the deadline. `charge`,
  `enter_frame` and `set_frame_cost` then check the work limit and after it
  their own limit (`max_frames`, or the retained totals at scope `Frame`);
  `charge_output` checks `max_output_bytes` before the work limit. Only a
  failed work check reads the clock once more; a failed check of an entry's
  own limit reports that limit without a reading, so an expiry that the
  polling step did not observe does not take precedence over it. An entry
  writes only when every check has passed, and a failed charge changes only
  the polling state: the credit of small charges and an observed expiry.
- The charge points are `charge`, `charge_output`, `enter_frame` and
  `set_frame_cost`. `reserve`, `release`, `leave_frame` and the checks are
  not charge points: they poll neither the probe nor the clock.
- A charge pays for work that is cooperative: a running primitive operation,
  allocation or formatting is not interrupted, and the context makes no
  promise about CPU time or memory.

### Reading the clock

- **When.** While a deadline is set and no expiry has been observed, a charge
  that observes no cancellation reads the clock when it is the first charge
  after the deadline was set, when its amount is zero, when its amount is at
  least 64 units (before the work it pays for), when it follows such a large
  charge, and when the 63 counted charges before it made no polling reading.
  So at most 63 consecutive charges make no polling reading, and none follows
  a large charge. When the work does not fit, the clock is read once more,
  without changing the credit, and an expired deadline takes precedence over
  exhausted work.
- **An observed expiry is final.** Every later charge fails with
  `DeadlineExceeded` without reading the clock, until `with_deadline` or
  `with_timeout` sets a deadline again; setting one resets the credit, so the
  next charge reads the clock.
- **Overrun bound.** The work charged after the deadline passes, before a
  charge fails with `DeadlineExceeded`, is at most $\max(4032, L)$ units,
  plus one primitive operation that is running when the deadline passes.
  Here $L$ is the amount of the last large charge that read the clock before
  the deadline, and $L \le$ `max_work`. A small or zero charge that read the
  clock is followed by at most 63 small charges without a reading, each below
  64 units, so its own work and theirs are at most $64 \cdot 63 = 4032$
  units; a large charge reads before its work, and the next charge reads
  again, so the work after its reading is its own amount $L$.
  `overrun_bound(L)` computes the bound.
- **Without a deadline** no clock is read.

### Injection

- `Clock::now()` returns nanoseconds as a `u64`, from an origin of the clock's
  own choosing, and never decreases. `CancelProbe::is_cancelled()` is polled
  first at every charge point; once it answers `true` it keeps doing so. Both
  traits are `Send` and keep a `fork()` method, which the context of this
  release never calls, for the sub-budgets of a later release.
- The defaults are `MonotonicClock`, based on `std::time::Instant` and
  measured from its creation, and `CancelFlag`, a shared `Arc<AtomicBool>`.
  The context holds the clock and the probe in an opaque adapter, the only
  place with shared state.
- `with_deadline(at)` takes a reading of the context's own clock;
  `with_timeout(nanos)` reads the clock once and sets the deadline `nanos`
  later, stopping at `u64::MAX`. `with_deadline` and `Clock::now` do not
  follow
  [convention 17](../../conventions/public-api.md#17-no-implicit-conventions):
  they state only in their documentation that a reading counts nanoseconds
  from an origin of the clock's own choosing, and neither `at` nor a reading
  names its unit. No documentation states whether a reading equal to `at`
  reaches the deadline; the context counts it as reached.
- Tests that depend on when the deadline passes or on the count of polls
  inject a fake clock and a fake probe through `Context::with_observers`. The
  tests of the default flag, the two host tests and the carried-over examples
  whose deadline is the current reading or an hour away use `Context::new`;
  no test depends on the speed of a clock. There are no test hooks inside
  charging and no global or thread-local state.

### Frames and temporaries

The context keeps one frame table, allocated at the first frame and keeping
its capacity, with one entry per open frame: its cost, a `Storage`, and its
generation number. Plain fields hold the sum of the frame costs,
`frames_total`, the sum of the reserved temporaries and the count of frames
entered, which numbers the generations. Three invariants hold after every
operation:

1. `frames_total` equals the sum of the costs in the frame table;
2. `frames_total` plus the temporaries is at most `max_nodes` in nodes and
   at most `max_storage_bytes` in bytes, so that sum never overflows;
3. the count of frames entered is at most the work used, since every frame
   entered charged one unit, so it never overflows.

| Operation | Charge | Check | Effect |
| --- | --- | --- | --- |
| `enter_frame()` | 1 unit | fewer than `max_frames` frames are open; otherwise `Field(Frames)`, no scope | opens a frame of cost zero and returns a `Frame` |
| `set_frame_cost(&frame, cost)` | 1 unit | the other frames, the temporaries and `cost`; scope `Frame` | replaces the cost of an open frame |
| `reserve(cost)` | none; not a charge point | the frames, the temporaries and `cost`; scope `Temporary` | returns a `Reserved` |
| `release(reserved)` | none | none | returns the reservation |
| `leave_frame(frame)` | none | none | closes the frame and every frame opened after it |
| `check_storage(cost, scope)` | none | the frames, the temporaries and `cost`; scope `scope` | none |
| `retained()` | none | none | reads the frames plus the temporaries |

- **Check, then write.** Every operation polls, charges and checks before it
  writes anything. A rejected frame or frame cost is not charged, and the
  frame table and `frames_total` stay unchanged. Recording a cost replaces
  the earlier cost and may target any open frame, not only the innermost. A
  zero reservation is not checked; since every write is checked first, the
  retained total never exceeds the limits, so this cannot be observed.
- **Reporting.** A storage check compares the nodes with `max_nodes`, then
  the bytes with `max_storage_bytes`, and fails with `Field(Nodes)` or
  `Field(StorageBytes)` and the scope of the check; when both are exceeded it
  reports `Nodes`. The amount is the exact total that was needed, or
  `Bound(u64::MAX)` when it does not fit in a `u64`.
- **Scope.** Exactly the two retained totals are reported with a scope: a
  single private constructor builds every limit record with a scope, and it
  takes one of those two fields. Work, output bytes, frames, the other fields
  of `check` and parameters have no scope.
- **Bounded work.** `check_storage`, `reserve`, `set_frame_cost` and
  `retained` take constant time, whatever the number of open frames.
  `leave_frame` is the only loop: one step per frame it closes, each of which
  was charged one unit when it was entered. So the work budget bounds the
  work of the context, up to a constant factor.
- **Tokens and generation numbers.** `Frame` and `Reserved` cannot be cloned,
  and compile-time guards keep it so. A `Frame` records the index of its frame
  and its generation number, the count of frames entered before it in the
  context. A token whose frame is no longer open, because its generation does
  not match the entry at its index or the index is past the open frames, is
  stale: `set_frame_cost` charges one unit and writes nothing, `leave_frame`
  closes nothing, and `frame_cost` is `None`. A stale inner token therefore
  never reaches a frame that was opened after its own frame was closed. Tokens
  belong to the context that issued them.
- **Exits that do not end the request.** A method that holds tokens and ends
  without ending the request must return them; only a request failure on the
  `Err` side may leave tokens unreturned. A copyable `mark()`, recording the
  frame count, the generation and the temporaries, and `restore(mark)`, which
  closes the frames opened since like `leave_frame` and restores the
  temporaries, arrive with the first method that holds tokens and can stop
  with a result state, no later than 0.3; that method restores the mark taken
  on entry when it stops. They are not part of this release.

### Bounded output

`charge_output(bytes)` polls as a charge of `bytes` units, then checks the
request's cumulative output against `max_output_bytes`, then charges one work
unit per byte, and records both only when every check has passed. A caller
writes bytes only after every charge for them has succeeded, so a failure
leaves no partial output.

### Sub-computations

A sub-computation charges the same `&mut Context` as its caller, in a fixed
order. The total work is the sum of the parts, and the result is
deterministic, but which part fails first depends on the order. There is no
way to allot a budget to a part and no `remaining_work()`. Until sub-budgets
arrive, sub-computations that share a context never run in parallel, and the
library starts no threads.

### What the context does not hold

- `settings` and `settings_version` are inputs of the request, and a progress
  receiver is a separate parameter of a streaming entry.
- Within the package, only the command entry and the command-line program
  may create a `Context`; the command entry never does: the caller of
  `execute`, such as the command-line program, creates one context per
  request. The guard of
  `cargo xtask check` rejects every path `Context::name` elsewhere in
  non-test code, so library code reaches the context only through the methods
  of the value it was given. `check` and `check_parameter` are `&self`
  methods for that reason.
- A `Context` cannot be cloned and does not implement `Default`.

## Testing obligations

1. **Requirements.** One positive and one negative test per requirement, as
   each entry above names them.
2. **No hidden caps.** One test per field, `no_hidden_cap_on_<field>`, sets the
   field beyond the caps of the earlier implementation (depth and frames 9,
   65, 129 and 257; the other fields $2^{40}$, and the exponent also 257) and
   checks that the value is admitted and the next one rejected, naming the
   field.
3. **Determinism.**
   `the_same_request_twice_charges_the_same_work_and_gives_the_same_result`
   runs one request twice under the same limits and compares the result, the
   work, the clock readings, the polls and the retained total;
   `charges_do_not_depend_on_the_budget` checks that the charges do not
   depend on `max_work`.
4. **Deadline.** With a fake clock,
   `a_deadline_right_after_a_large_charge_reading_overruns_by_at_most_the_bound`
   lets the deadline pass right after the reading of a large charge and checks
   that the overrun is the large amount and within `overrun_bound`.
5. **Host.** `host_cancelled_between_two_evaluations` cancels the default flag
   from another thread between two evaluations, and `host_deadline_expires`
   lets a deadline of one millisecond on the monotonic clock pass.
6. **Frames and temporaries.** The tests of `tests/context.rs` and
   `src/context/tests.rs` check the scopes, the replacement of costs,
   truncation, stale tokens, exact sums at the `u64` width and the two
   invariants of the frame table.
7. **No message text.** No test asserts the message of an error.

## Extractability

The core of the component is written to follow the provable subset of Rust
that Charon and Aeneas translate into Lean 4. It is, all in
`src/context.rs`:

- charging: `charge`, `charge_at`, `charge_output` and the private steps
  `observe`, `poll_deadline`, `admit_work`, `exhausted`,
  `deadline_reached` and `admit_output`;
- the deadline: `with_deadline`, and `with_timeout`, which reads the clock;
- the accounting of frames and temporaries: `enter_frame`, `push_frame`,
  `set_frame_cost`, `write_frame_cost`, `leave_frame`, `truncate_frames`,
  `without_frames`, `frame_cost`, `frame_count`, `retained`, `reserve` and
  `release`;
- the checks: `check`, `check_at`, `check_bound_at`, `check_width_at`,
  `check_parameter`, `check_storage`, `check_storage_at`, `admit`, `fit`,
  `retained_exceeded` and `field_exceeded`.

The core uses `match` instead of combinators with closures and instead of
`if let`, no iterators and no closures, one index loop in a helper of its
own, checks before the first write, no mutable borrow of the frame table
across a write to another field, and no interior mutability, which only the
observer adapter in `src/context/observer.rs` has. Three parts do not follow
the subset's design rules and are left for the upgrade to tier A3: the frame
table allocates at run time (a `Box<Vec<..>>`), which needs proof models of
`Vec` and `Box`; every failure allocates, since the errors component builds
each request failure with an owned message and `check_parameter` copies the
parameter name into a `String`, which needs a model of `String`; and the
clock and the probe are boxed trait objects in the adapter, which the
extraction is to cut. None of this code has been extracted: no proof target
is registered for it yet.

The module list of the component, the files that the `subset` step of
`cargo xtask check` checks against the provable subset and that
`cargo xtask formal check` inventories, holds the accounting core; the limits,
the storage and the observer adapter below `src/context/` are not listed:

```paths
src/context.rs
```

## Current deviations

None: the code and the tests follow every rule above.
