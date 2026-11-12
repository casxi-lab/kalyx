# Errors and result states

This contract states how a kalyx request reports that it has no answer, an
`Error`, and how a method reports a meaningful outcome that is not a complete
answer, a mathematical state carried by `Settled<T>`. It applies to the types
in `src/error.rs` and to every function of the library that returns them. The
[architecture](../../architecture.md#error-kinds) places the component among
the foundations, and the
[public API conventions](../../conventions/public-api.md) state the rules that
every public interface follows; conventions
[2](../../conventions/public-api.md#2-errors-separate-from-result-states),
[6](../../conventions/public-api.md#6-no-hidden-caps),
[7](../../conventions/public-api.md#7-iteration-caps-are-result-states),
[11](../../conventions/public-api.md#11-no-unchecked-constructors) and
[14](../../conventions/public-api.md#14-canonical-representation-and-equality)
concern errors and states and are not restated here.

**Status.** Implemented in `src/error.rs`, at tier A1 (tested with a written
contract). The request context, the only code that constructs request
failures, returns them from its charge points and checks. The exact numbers
(`kalyx::number` and `kalyx::coefficient`) are the first entries of the
library that compute: they return the faults `DivisionByZero`, `Syntax` and
`Internal` and the request failures of the context, and the integer kernel of
the exact numbers returns `OutsideDomain` as well. The first public method
with result states comes with a later release. The crate-internal channel and its boundaries are
exercised by the unit tests of `src/error.rs`.

## Interface

The crate root re-exports every public item of the component:

- `Error`, with the accessors `kind()`, `span()`, `message()` and
  `exceeded()`, the constructor `Error::new(kind: FaultKind, span, message)`,
  `Display` and `std::error::Error`;
- `ErrorKind` (`ResourceLimit`, `Cancelled`, `DeadlineExceeded`,
  `Fault(FaultKind)`), `FaultKind` and `ErrorClass`, with `class()` on both
  kind enums;
- `LimitExceeded`, with the accessors `id()`, `scope()`, `allowed()` and
  `amount()`, and `LimitId`, `LimitField`, `LimitScope` and `LimitAmount`;
- `Span`, a half-open byte range with `Span::new(start, end)`, which is `None`
  when `end < start`;
- `MathState` and `Settled<T>`, with the accessors `value()`, `into_value()`,
  `state()`, `is_value()` and `is_state()`;
- `Result<T>`, which is `std::result::Result<T, Error>`.

Crate-internal, for the request context, for the parser and for methods with
states:

- the constructors of the three request failures, `Error::resource_limit`,
  `Error::cancelled` and `Error::deadline_exceeded`, and
  `LimitExceeded::new`;
- `Error::with_default_span(span)`, which gives an error that has no span the
  span `span` and keeps the span of an error that has one, and changes
  nothing else: the [parser](../syntax/contract.md#spans) gives each error of
  the term core, which carries no span, the span of the syntax node whose
  term failed;
- the internal channel `Run<T>`, a `Result` whose error type `Halt` is either
  `Error(Error)` or `Stop(MathState, Cap)`, with `From<Error> for Halt`;
- `Cap` and its diagnostic text `Cap::message`;
- the boundaries `settle` and `evaluation_stop`.

## Requirements

The requirement identifiers are those of the earlier implementation of the
casξ computer algebra system; they are never renumbered or reused. Each entry
states the part of the requirement that concerns errors and result states,
where kalyx implements it and which component owns the rest.

### CTX-R09

**Iteration caps are result states.** Reaching an iteration cap that belongs
to a method or its options returns `Ok` with a state of the result; it is
never an error and never causes one. No `ErrorKind` stands for a cap or for
any other state. A cap reached in an inner computation becomes a state of the
outer result, a request failure of an inner computation stays the same error,
and a classification of the outer method never applies to an error of a
request kind and never turns an error into the state of a cap.

- **Implemented here.** `ErrorKind` has no state among its kinds, and
  `MathState` has no request failure among its states. The internal channel
  carries a stop as `Halt::Stop(state, cap)`, `?` ends the computation at the
  first halt, and there is no conversion from `Halt` to `Error`. The
  boundaries `settle` and `evaluation_stop` turn a stop into a state and keep
  every error with its kind, span, exceeded limit and message. Since
  `Error::new` cannot build a request failure, an error of a request kind that
  a classification sees always comes from the request context.
- **Owned elsewhere.** The iterative methods with caps of their own, their
  inner caps and their classifications come with the numerical kernel and
  evaluation framework, planned for 0.3, and with the method families after
  it.
- **Evidence.** `settle_partitions_runs_into_values_states_and_errors`,
  `evaluation_stop_keeps_stops_and_errors_and_names_caps`,
  `each_math_state_settles_into_a_state` and
  `a_math_state_is_never_an_error_and_a_value_never_a_state` in
  `src/error.rs`.

### NUM-R10

**Request failures take precedence over every state.** Of this accounting
requirement, the clause that concerns errors and states is: a failure of the
request context takes precedence over every result state.

- **Implemented here.** Request failures are on the `Err` side and states
  inside `Ok`, so the precedence holds by the types: a computation that meets
  a request failure returns it, whatever state it would otherwise have
  reached, and `settle` and `evaluation_stop` never turn an error into a
  state.
- **Owned elsewhere.** The charges themselves belong to the
  [request context](../context/contract.md); that every operation and every
  series step charges the context belongs to the components that perform
  them, such as the numerical kernel and evaluation framework, planned for
  0.3.
- **Evidence.** `faults_are_never_of_the_context_class_and_errors_never_states`
  in `src/error.rs`.

### NUM-R02

**An undecided interval operation is a state.** Of this interval-arithmetic
requirement, the clause that concerns errors and states is: the reciprocal of
an interval that contains zero but is not the point zero is the undecided
state, while the point zero is a `DivisionByZero` error.

- **Implemented here.** The state `MathState::Undecided` and the fault
  `FaultKind::DivisionByZero`. No error kind stands for an undecided outcome,
  so the earlier implementation's report of this state as an error cannot
  recur.
- **Owned elsewhere.** Interval arithmetic comes with the numerical kernel and
  evaluation framework, planned for 0.3.
- **Evidence.** `each_math_state_settles_into_a_state` in `src/error.rs`.

### CTX-R02

**Priority of request failures.** When one charge of the request context
meets several request failures, it reports cancellation, then a deadline
that the context has observed to pass, then an exhausted limit; when the
context reads its clock is part of its contract. The error carries the span
that the caller of the charge gave; its message is not part of the
requirement.

- **Implemented here.** The three request kinds, and their crate-internal
  constructors, which take the caller's span.
- **Owned elsewhere.** The order of the checks belongs to the request
  context, whose [contract](../context/contract.md#ctx-r02) states it.
- **Evidence.** `request_failures_are_errors_of_the_context_class` in
  `src/error.rs`.

## Rules

### Request failures and faults

- An `Error` means that the request has no answer. Its kind is a request
  failure (`ResourceLimit`, `Cancelled` or `DeadlineExceeded`) or a
  `Fault(FaultKind)`.
- The foundation faults are `Syntax`, `UnknownSymbol`, `DivisionByZero`,
  `NonIntegerExponent` (the exponent is not an integer constant),
  `NotPolynomial`, `Unsupported` and `Internal`. A feature adds a kind of its
  own in the release that brings the feature, after the kinds before it: the
  integer kernel of the exact numbers added `OutsideDomain`, an argument
  outside the domain of an operation, in release 0.2. `ErrorKind` and `FaultKind` are
  `#[non_exhaustive]`, so code outside the library matches them with a
  wildcard arm.
- `class()` sorts every kind into one of three classes: `Context` for the
  request failures, which a larger limit, a later deadline or no cancellation
  may lift; `Internal` for `FaultKind::Internal`, a defect of the library; and
  `Input` for every other fault. A fault is never of class `Context`.
- The fields of `Error` are private. `exceeded()` is `Some` exactly when the
  kind is `ResourceLimit`; the representation keeps the record inside that
  case, so no error has one without the other.
- Programs act on `kind()`, `span()` and `exceeded()`. The message is text for
  people, so `Error` implements neither `PartialEq`, `Eq` nor `Hash`, and
  tests compare those three parts, never the message.

### Constructing errors

- `Error::new(kind: FaultKind, span, message)` takes only a `FaultKind`.
  `Error::new(ErrorKind::Cancelled, ..)` does not compile, failing with error
  `E0308` (mismatched types); the documentation of `Error::new` holds this
  call as a `compile_fail,E0308` test, next to the same call with a
  `FaultKind`, which compiles.
- Only the request context constructs request failures, through
  crate-internal constructors that take the span of the caller of the failed
  check and build a fixed message.
- `LimitExceeded` has no public constructor.

### Limit identifiers

A `ResourceLimit` error carries a `LimitExceeded`: the limit's identifier, its
scope, the allowed value and the amount.

- **Identifier.** `LimitId::Field(field)` names a field of `Limits`; the nine
  variants of `LimitField` correspond to the nine fields, and
  `LimitField::name` gives the field name, such as `max_work`. A bound
  derived from a field names that field. `LimitId::Parameter(name)` names an
  explicit parameter of the request, with the name as an owned string.
- **Allowed value.** The `u64` value of the limit that was in force.
- **Amount.** `LimitAmount::Used` is the total at the check that failed,
  `Required` the exact amount needed, and `Bound` a reliable upper estimate
  beyond the allowed value, `u64::MAX` when the amount does not fit.
- **Scope.** For `Nodes` and `StorageBytes`, `scope()` says where the limit
  was reached: `Value` (building or admitting a value), `Frame` (the cost of
  an open frame) or `Temporary` (a reserved temporary). The frame limit and
  the temporary limit are the same totals checked at two places, so they are
  told apart by the scope, not by the identifier. For every other field and
  for a parameter the scope is `None`; the number of open frames is the
  separate field `Frames`.
- The record derives `PartialEq` and `Eq`, so tests compare it whole.

### Bounds set by a machine width

A bound that a machine width imposes is reported as the field or parameter
that dominates it, with `allowed` its effective value. A bound that no field or
parameter dominates is never a `ResourceLimit`: a method that gives up returns
the state `NotApplicable`, and an unreachable counter overflow is an
`Internal` error. So a `ResourceLimit` error can always be lifted by changing
one named field or parameter.

### Mathematical states

- `MathState` is `NotConverged`, `Unevaluated`, `NotApplicable`, `Undecided`
  or `IterationLimit`, and is `#[non_exhaustive]`. A state is a value inside
  `Ok`, never a request failure.
- `Settled<T>` is `Value(T)` or `State(MathState)`, `#[non_exhaustive]` and
  `#[must_use]`. A method without states returns `Result<T>`, and a method
  with states returns `Result<Settled<T>>`.
- Inside the library, a computation that can stop in a state returns
  `Run<T>`. A stop is `Halt::Stop(state, cap)`: the state that the stop means
  for the method, and the cap at which it stopped. `?` converts an `Error`
  into a `Halt`, so the first failure or stop ends the computation and nothing
  after it runs.
- There is no conversion from `Halt` to `Error`. Each method decides at a
  boundary what a stop means for its result.
- **Boundary rule.** At every boundary a stop becomes a state, never an
  error, and every error stays the same error, with its kind, span, exceeded
  limit and message, never a state. `settle` turns a value into
  `Settled::Value` and a stop into `Settled::State` with the stop's state.
  `evaluation_stop(run, capped)` keeps the stop value that a method reached
  and turns a stop of one of its evaluations into the method's own stop value
  `capped`.
- **Precedence.** A request failure is on the `Err` side, so it takes
  precedence over every state by its type.

### Caps in this release

`Cap` names where a cap was reached and gives its diagnostic text. No method
of this release has a cap of its own, so `Cap` has one general variant,
`IterationBound`: a method reached the iteration bound that its caller gave
it. Its text is `iteration bound reached`. The caps of the earlier
implementation, an elementary series that did not reach its error target and
the scaling steps of a matrix exponential, belong to features that kalyx does
not have yet. A method family that brings a cap adds a variant naming its
place, with a fixed text, in the release that brings it.

### Messages

- Messages are English and built as owned strings, by `String::from` from a
  fixed text or by appending a name to one. Code meant to be proved returns no
  string literal. No message embeds the `Debug` rendering of a value.
- The request failures read `computation cancelled`, `deadline exceeded` and
  `resource limit exceeded: ` followed by the name of the limit, the field
  name or the parameter name.
- The diagnostic text of a cap, which `Cap::message` gives, is fixed per
  variant.
- Messages are not part of the interface, except that the result-state
  functions that a contract gives a fixed text keep it.
- **The inner integrations of a dynamic fit.** This function belongs to a
  later release; the rule for its message is fixed now. When an inner
  integration of a dynamic fit ends with a stop other than reaching its end, a
  stop of an evaluation or one of the step, rejection and event limits, the
  fit reports it with the fixed text
  `dynamic fit inner integration incomplete`, built by `String::from`, with
  nothing appended: in particular not the `Debug` name of the stop, which
  turned the message of the earlier implementation into text that varied with
  the stop. A program that needs the stop reads it from a structured field,
  not from the text. The kind or state that reports it follows the
  [mapping](#kinds-of-the-earlier-implementation) of the former
  `IntegrationFailure` and is fixed by the contract of the component that
  brings dynamic fitting. If that is an error, the fixed text is its message.
  If that is a state, which carries no text, the fixed text is the diagnostic
  text, `Cap::message`, of the cap variant at which the fit stops.

## Kinds of the earlier implementation

The earlier implementation had one enum of 25 error kinds that mixed request
failures with mathematical outcomes. Each kind has this place in kalyx:

| Former kinds | In kalyx | First producer |
| --- | --- | --- |
| `ResourceLimit`, `Cancelled`, `DeadlineExceeded` | `ErrorKind`, same names (request failures); `ResourceLimit` carries a `LimitExceeded` | the request context, 0.1 |
| `Syntax`, `DivisionByZero`, `UnknownSymbol`, `NotPolynomial`, `NonIntegerExponent` | `FaultKind`, same names (foundation faults) | the parser, exact numbers, the term core and the polynomials over $\mathbb{Q}$, 0.1 |
| `UnsupportedSymbolic`, `UnsupportedValue` | merged into `FaultKind::Unsupported`; collection values may add a finer kind of their own | the term core (reserved names), the parser and the command entry, 0.1 |
| `NonConstantExponent` | merged into `NonIntegerExponent`, which means that the exponent is not an integer constant | the parser, 0.1, since the powers of the term core take an integer exponent |
| `OutsideDomain` | `FaultKind::OutsideDomain`, a feature kind appended under the same name | the integer kernel of the exact numbers, 0.2 |
| `ContradictoryAssumptions`, `InvalidBinding`, `VariableMismatch`, `InvalidInterval` | feature kinds, appended under the same names | the term core extension with assumptions, the function-expression baseline, coefficient fields, and real sets and inequalities, 0.2 |
| `StaleEnvironment`, `DimensionMismatch` | feature kinds, appended under the same names | the computation environment with versioned requests, and the arrays of collection values, 0.3 |
| `InvalidMatrix`, `SingularMatrix` | feature kinds, appended under the same names | exact rational matrices and linear systems, 0.4 |
| `FactorizationFailure`, `RootIsolationFailure` | `FaultKind::Internal` when a self-check fails; `MathState::NotApplicable` when the method legitimately gives up | polynomial factorization and real root isolation, 0.2 |
| `InfiniteRoots` | `OutsideDomain`; a value instead, if real root isolation reports "every point" through a completeness result | real root isolation, 0.2 |
| `Indeterminate` | `MathState::Undecided`, which removes the deviation recorded for NUM-R02 | the numerical kernel, 0.3 |
| `IntegrationFailure` | `FaultKind::Internal` when the check of an exact antiderivative fails; `MathState::NotConverged` when numerical integration misses its tolerance | symbolic calculus, 0.5 |

The merges change the kinds that the answer vectors of later releases expect;
the mapping above is fixed, so each difference is accepted by its row.

## Testing obligations

1. **Boundaries.** The unit tests in `src/error.rs` check that `settle` keeps
   values, turns a stop in each of the five states into that state and keeps
   every request failure, a domain error and an invalid input with its kind,
   span and exceeded limit, and that no foundation fault becomes a state;
   that `evaluation_stop` keeps stops and errors and turns every stop into the
   given stop; the fixed text of the cap; the accessors of `Settled`; and
   that `with_default_span` fills only a missing span
   (`a_default_span_fills_only_a_missing_span`).
2. **Two types.** For request failures and for mathematical states, one
   positive and one negative test each:
   `request_failures_are_errors_of_the_context_class`,
   `faults_are_never_of_the_context_class_and_errors_never_states`,
   `each_math_state_settles_into_a_state` and
   `a_math_state_is_never_an_error_and_a_value_never_a_state`.
3. **Limit identifiers.** `resource_limits_carry_structured_identifiers`,
   `frame_and_temporary_limits_differ_by_scope`,
   `a_request_parameter_limit_names_the_parameter` and
   `only_a_resource_limit_has_an_exceeded_limit` assert the identifier, the
   scope, the allowed value and the amount structurally.
4. **Construction.** The `compile_fail,E0308` documentation test of
   `Error::new` rejects a request kind, and
   `error_new_builds_faults_and_never_request_failures` in `tests/errors.rs`
   builds every fault kind.
5. **Public interface.** `tests/errors.rs` checks the public interface as code
   outside the library sees it: errors that such code constructs, the
   standard error trait, the `Display` form (the message, then the span),
   spans, the names of the limit fields and `Settled`.
6. **No message text.** No test asserts the message of an `Error`.

## Extractability

The four functions of the result-state core, `settle`, `evaluation_stop`,
`Cap::message` and `From<Error> for Halt`, are written to follow the provable
subset of Rust that Charon and Aeneas translate into Lean 4. `settle`,
`evaluation_stop` and `Cap::message` are each one `match` on an argument taken
by value, and `From<Error> for Halt` is one constructor. None has a loop,
closure, combinator, function value, borrow or `?`, and the only allocation is
the owned string of `Cap::message`, built by `String::from`. They have not
been extracted: no proof target is registered for them yet.

The module list of the component, the files that the `subset` step of
`cargo xtask check` checks against the provable subset and that
`cargo xtask formal check` inventories, holds the errors and result states:

```paths
src/error.rs
```

## Current deviations

None: the code and the tests follow every rule above.
