# Public API conventions

These fifteen conventions govern every public interface of the kalyx
library: functions, methods, types and the crate root. They also apply to
crate-internal interfaces that a public entry reaches, wherever the
convention is about behavior (limits, determinism, panics, depth).

**Status.** The library's only public items so far are the types of its
errors and result states, the request context with its limits, the exact
numbers with the coefficient-field trait over $\mathbb{Q}$, the terms of the
term core, the parser, the univariate polynomials and the command entry,
which follow these conventions. They are the rules that each further
component follows when it lands, and review holds every change to them.
`Error`, `Settled<T>`, `LimitId`, `MathState`, `Context`, `Limits`,
`Integer`, `Rational`, `ZeroTest`, `CoefficientRing`, `CoefficientField`,
`Rationals`, `Term`, `TermKind`, `parse`, `PolynomialRing`, `Polynomial`,
`Request`, `Settings`, `Outcome`, `execute` and `serialize` exist today;
other names used here are the names that the code is planned to use. Their
full rules are in [the architecture](../architecture.md). `cargo xtask check`
already enforces the parts that it can check mechanically, as each convention
below states: see [CONTRIBUTING](../../CONTRIBUTING.md#checks).

Each convention ends with a counterexample from the earlier implementation of
the casξ computer algebra system, which is not public. A counterexample is
cited as `cas-project@<full commit SHA>:<path>:<line>`, where `cas-project`
names the earlier implementation. Counterexamples show what a convention rules
out; none of that code is taken over.

1. [Request context last](#1-request-context-last)
2. [Errors separate from result states](#2-errors-separate-from-result-states)
3. [Extensible enums and records](#3-extensible-enums-and-records)
4. [Limits built from defaults](#4-limits-built-from-defaults)
5. [Uniform parse signature](#5-uniform-parse-signature)
6. [No hidden caps](#6-no-hidden-caps)
7. [Iteration caps are result states](#7-iteration-caps-are-result-states)
8. [Determinism](#8-determinism)
9. [No global state](#9-no-global-state)
10. [Bounded output](#10-bounded-output)
11. [No unchecked constructors](#11-no-unchecked-constructors)
12. [No panic](#12-no-panic)
13. [Request inputs and progress](#13-request-inputs-and-progress)
14. [Canonical representation and equality](#14-canonical-representation-and-equality)
15. [Depth](#15-depth)

## 1. Request context last

Every public function or method that may allocate, iterate, recurse or
produce output takes the request context, `context: &mut Context`, as its
last parameter. It returns `Result<T>`, which is
`std::result::Result<T, Error>`, or `Result<Settled<T>>` when it has result
states ([convention 2](#2-errors-separate-from-result-states)). A method of a
parent structure, such as a coefficient field or a polynomial ring, takes the
structure as `&self` and the context last as well.

A library function never creates a context in place of the caller's. Within
the package, only the command entry and the command-line program may
construct a `Context`, and the guard of `cargo xtask check` rejects every
other construction path that it can see; in this release neither does: the
caller of `execute` creates one context per request, and library code
charges the context that it is given.
Library interfaces return library types: parsing command-line options and
choosing process exit codes belong to the program. The command entry is the
one exception to the return type: `execute` returns an `Outcome`, which
holds the `Result<Settled<T>>` of the request together with its versions, so
that the versions come back with every error as well.

**Counterexample in the earlier implementation.**
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/command.rs:555` and
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/command/integer.rs:131-157`.
The public library entry `single(command, args)` returns
`Result<String, (u8, String)>` and takes no context: the handler parses a
`--work` option itself, builds default limits and a context of its own, and
maps every error to process exit code 1 or 2. A caller cannot pass its own
limits, cancellation or deadline, and the error kind is lost.

## 2. Errors separate from result states

An `Err(Error)` means that the request has no answer: the input is invalid, a
domain error such as division by zero occurred, a limit was exhausted, the
request was cancelled or its deadline passed. An outcome that is meaningful
but not a complete answer is a mathematical state, returned inside `Ok`:
`Settled<T>` is either `Value(T)` or `State(MathState)`, and `MathState` is
not converged, unevaluated, method not applicable, undecided or iteration
limit reached.

Request failures and mathematical states are separate types. No `ErrorKind`
stands for a mathematical state, and no `MathState` stands for a request
failure. Because request failures are on the `Err` side, they take precedence
over any state by their type.

**Counterexample in the earlier implementation.**
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/error.rs:14-40`.
One enum of 25 error kinds holds request failures such as `ResourceLimit`,
`Cancelled` and `DeadlineExceeded` together with mathematical outcomes such as
`FactorizationFailure`, `Indeterminate`, `IntegrationFailure` and
`RootIsolationFailure`. A caller cannot tell from the type whether the request
did not finish, which more budget may fix, or whether the method reached no
conclusion, which needs another method.

## 3. Extensible enums and records

Every public enum is `#[non_exhaustive]` unless it is a closed case analysis
listed here with its reason. The one listed exception is `ZeroTest` (zero,
nonzero or undecided) of the coefficient-field trait, whose three cases are
mathematically complete. Every public record with public fields is
`#[non_exhaustive]`; other structs keep their fields private.

The crate root re-exports only request-level items: the context and its
limits, errors and result states, the request and outcome types, the command
entry `execute`, and `parse`.
Component types are reached through their component's module. The root
re-exports neither command-language types nor third-party types. The public
names of the crate root are listed in the tracked file `api/root-names.txt`,
and the test `the_crate_root_has_exactly_the_listed_public_names` in
`tests/root_names.rs` fails when a public name is added to the crate root,
removed or renamed without the list being changed. A macro exported with
`#[macro_export]` would land in the crate root from any module, so the test
`no_file_under_src_exports_a_macro` rejects one in every file under `src/`.

**Counterexample in the earlier implementation.**
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/lib.rs:41-147`.
The crate root flatly re-exports 298 public names through `pub use`,
including the operand and operation enums of the command language and the
third-party type `num_rational::BigRational` as `Rational`. Every feature
widens the root namespace, and adding, removing or renaming any of these
types is a breaking change at the root that `#[non_exhaustive]` cannot
prevent.

## 4. Limits built from defaults

`Limits` is a record in which every field has a documented default. Callers
start from `Limits::new()` or `Limits::default()`, which give the same
values, and change single fields with `with_<field>` methods. A new limit is
added only as a new field with a default; the number of fields is at most
ten, fixed by a compile-time assertion.

Library code below the command entry never constructs `Limits` or `Context`.
It uses the context that it was given, so the caller's limits, deadline and
cancellation apply to all of its work, and all of its work is charged to the
request.

**Counterexample in the earlier implementation.**
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/symbolic/functions/heads.rs:94-110`.
To build the degree literal of an $n$th root, the code creates a separate
context from default limits, "so the caller's context is not charged for it",
and calls `expect` on the result. That work escapes the caller's limits,
deadline and cancellation.

## 5. Uniform parse signature

A function named `parse` or `parse_<what>` reads text in the library's input
syntax and has the shape

```rust
fn parse(source: &str, /* values that fix the interpretation */ context: &mut Context) -> Result<T>
```

The source text comes first, then the values that fix its interpretation,
such as variables, a domain or a ring, then the context. A method takes its
receiver before these as usual. A syntax error carries the byte span of the
offending text in the source. Selecting a fixed keyword uses `FromStr` and is
not called `parse`.

**Counterexample in the earlier implementation.**
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/linear_algebra/parameter_matrix.rs:133-138`.
`ParameterMatrix::parse` takes the ring, the domain, the source text and the
context in that order, while `AlgebraicMatrix::parse` in the same family takes
the source text first. Callers and generated bindings have to remember the
order for each type, and the meaning of a span differs between entries.

## 6. No hidden caps

Every limit is a field of `Limits` or an explicit parameter of the request,
and its value is applied as given. Code never clamps a limit with a constant,
as in `limits.max_x.min(N)`, never uses one field to bound a different
quantity, and never hard-codes the scale bound of a feature. A bound derived
from a general field is reported with that field as
`LimitId::Field(<field>)`; a bound that is a request parameter is reported
with the parameter name as `LimitId::Parameter(<name>)`.

A bound that a machine width imposes is written as the field or parameter
that dominates it. A bound that no field or parameter dominates is not
reported as `ResourceLimit`: a method that gives up returns the state
`MathState::NotApplicable`, and an unreachable counter overflow is an
`Internal` error. So a `ResourceLimit` error can always be lifted by changing
one named field or parameter.

**Counterexample in the earlier implementation.**
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/context.rs:438`,
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/context.rs:453`,
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/symbolic/functions/parser.rs:169`
and
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/expression.rs:198`.
Command nesting is bounded by `max_parse_depth.min(8)`, user calls by
`max_call_depth.min(64)`, and parsing by `max_parse_depth.min(128)` or
`max_parse_depth.min(256)`, depending on the path; non-test code clamps limit
fields with constants in more than twenty places. A caller who sets the parse
depth to 1000 gets 8, 128 or 256, and one field bounds several different
quantities.

## 7. Iteration caps are result states

An iteration cap is a parameter of the method or of its options, not a field
of `Limits`. Reaching it returns `Ok` with the state
`MathState::IterationLimit`, or with a state of the feature's own status type
that names `IterationLimit` as the state it refines. The cap is accepted as
given and is not checked against an unrelated limit such as a node count. The
work of every iteration is still charged against `max_work`, and
`ResourceLimit` names only a request limit that was actually exhausted.

**Counterexample in the earlier implementation.**
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/nonlinear/ivp.rs:143-153`.
The six iteration and event caps of the differential equation options are
each checked against the node limit and fail with `ResourceLimit` when they
exceed it. Under the default node limit of 8192, a request with at most 10000
steps fails before it starts instead of returning a step-limit state when the
steps run out.

## 8. Determinism

Given the same request, inputs and limits, a computation charges the same
work and returns the same result or the same error on every run, on every
host and under every thread schedule. Only the outcome of cancellation and of
a deadline may differ, since they depend on the injected probe and clock. The
amount of a charge depends only on the operands, never on the limits or on the
remaining budget. Neither results nor charges depend on pointer identity (such
as `Rc::ptr_eq`), on whether values share an allocation, on addresses, on hash
iteration order or on timing. The guard of `cargo xtask check` already
rejects hash containers, `RandomState`, `SystemTime` and threads in library
code.

**Counterexample in the earlier implementation.**
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/algebra/number_field.rs:93-98`.
Checking that two number fields are compatible returns early when both share
one `Arc`, and otherwise calls a charged comparison of the embeddings, while
the derived `==` compares contents. Two equal fields, one cloned and one built
again from the same data, are charged differently, so a request can succeed
or fail with `ResourceLimit` depending on how memory was shared.

## 9. No global state

The library has no global or thread-local mutable state, in any build
configuration. Everything that a computation reads comes from its
parameters: the inputs, the settings and the context. The clock and the
cancellation probe are injected through the context, and tests substitute a
fake clock and a fake probe there, never through hooks inside library code.
The guard of `cargo xtask check` already rejects `thread_local!`,
`static mut` and `SystemTime` in library code.

**Counterexample in the earlier implementation.**
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/context.rs:383-384`,
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/context/deadline_probe.rs:19-20`
and
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/context.rs:296-299`.
In test builds, every charge calls a hook that reads a thread-local variable,
and the deadline check reads the process clock directly. The behavior of a
charge depends on state outside its parameters, test and production builds
run different code, and deadline tests cannot inject a clock.

## 10. Bounded output

Public display and serialization take the context. They charge every output
byte and check cancellation at each charge point. Charging output first
checks the request's cumulative `max_output_bytes`, then charges one work unit
per byte. Exceeding a limit fails with `ResourceLimit` and produces no partial
output: bytes are written only after every charge for them has succeeded.

`impl Display` exists only as a debugging convenience and is never the path
by which results reach callers. The command entry has one serialization
function, `kalyx::command::serialize`, that writes an outcome as line bytes;
it is the only output format, and the command-line program is to call only
it.

**Counterexample in the earlier implementation.**
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/symbolic/display.rs:9-13`.
`impl Display` for symbolic expressions takes no context and renders the tree
recursively, yet it is the public output path: the command entry turns
results into strings with `to_string()`. Formatting a large result is
neither bounded, charged nor cancellable, and an error halfway through leaves
partial output.

## 11. No unchecked constructors

Every public way to build a value establishes the invariants of its type:
constructors validate and normalize their inputs and return `Result`, or
`Option` when the only failure is an invalid combination of arguments for
which no error kind applies, as for `Span::new` when `end` is less than
`start`. There are no public `new_unchecked` or `new_raw` constructors, no
public fields that carry an invariant, and no re-exported third-party types
whose own interface offers such constructors. This includes errors:
`Error::new` accepts only a `FaultKind`, so `Cancelled`, `DeadlineExceeded`
and `ResourceLimit` are built only by the context, and the limit record of a
`ResourceLimit` has no public constructor.

**Counterexample in the earlier implementation.**
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/lib.rs:123`.
The crate root re-exports `num_rational::BigRational` as the library's
rational type, so callers can use its `new_raw`, which neither rejects a zero
denominator nor reduces the fraction. A value such as $1/0$ or an unreduced
$2/4$ can then reach every entry that accepts a rational and break canonical
forms and equality.

## 12. No panic

A library entry returns an error or a result state for every input and every
valid `Limits`; it never panics. A broken internal invariant is reported as an
error of kind `FaultKind::Internal`, not through `panic!`, `unwrap`, `expect`
or `unreachable!`. Implicit panics are prevented as well: arithmetic that can
overflow is checked, sizes are checked before allocating, and indexing stays
in range. `cargo xtask check` already denies explicit panics in non-test
code, and the release profile keeps overflow checks, so an unchecked overflow
is a panic, never a silently wrapped value.

**Counterexample in the earlier implementation.**
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/algebra/factorization/integer.rs:49-54`.
`small_residue` returns `Result`, yet when its internal invariant fails it
calls `panic!("reduced u32")`. A host that runs the library with
`panic = "abort"` loses every job in the process instead of receiving an
error.

## 13. Request inputs and progress

A request carries `settings`, a non-exhaustive record whose default is the
current semantics, and `settings_version`; the outcome echoes the version that
was used. Settings never live in the context or in global state. In release
0.1 the settings record, `kalyx::command::Settings`, is empty, so its default
is its only value, and a request with a non-default value fails with
`Unsupported`.

A streaming entry takes its progress receiver as a separate parameter.
Progress is never reported through the context or through global hooks.

**Counterexample in the earlier implementation.**
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/environment.rs:180-186`.
The request type holds only the input and environment versions and the
operation, and the result echoes only those versions. Choices that change the
meaning of a request, such as the number domain of an evaluation, are fixed in
the code, so adding a setting later means changing the request type or adding
a global switch, and a result does not show which semantics produced it.

## 14. Canonical representation and equality

Derived `PartialEq`, `Eq`, `Ord` and `Hash` are used only on canonical
representations, where structural equality is mathematical equality. Values
whose representation is not unique, such as intervals, enclosures and
algebraic-number or root certificates, do not derive equality; they are
compared by a method that takes the context. Values are normalized before
they are encoded or hashed, and equality and ordering never use pointer
identity. `Error` does not derive equality either, since it carries message
text: tests compare its kind, span and exceeded limit, never the message.

**Counterexample in the earlier implementation.**
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/numerical/interval.rs:6-12`.
The real enclosure type derives `Eq` over its endpoints and a precision
field. Two enclosures with the same endpoints and different precision compare
unequal, and so do two enclosures of the same real number, so caching,
deduplication or encoding by derived equality treats equal values as
different.

## 15. Depth

An algorithm that traverses a term or another nested value, including
formatting, comparison and drop, uses an explicit stack on the heap, or it
rejects the input at the entry by the `max_depth` field of `Limits` and
documents its stack use. Native recursion that is safe only because of a
constant bound is not allowed. Depth tests set `max_depth` to at least the
depth they test and traverse terms at that depth.

**Counterexample in the earlier implementation.**
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/symbolic.rs:41-56`
and
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/symbolic.rs:345`.
The symbolic term is a native tree without a custom `Drop`, and formatting and
comparison recurse natively; only the hidden cap
`max_symbolic_depth.min(128)` keeps the stack safe. Raising the depth limit
has no effect, and without the cap a deep term would overflow the stack when
it is dropped or formatted.
