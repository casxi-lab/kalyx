# Porting record

kalyx is built from its foundations. Some of its foundation code is to be
taken over from an earlier implementation of the casξ computer algebra system,
which is not public. This record lists every module taken over, one row per
module, added in the same change as the code.

- **Module**: the module in this repository.
- **Source**: the files it came from, written as
  `cas-project@<full commit SHA>:<path>`, where `cas-project` names the
  earlier implementation.
- **Change**: one of *ported* (taken over with only the changes that the
  rules of this repository require), *adapted* (interfaces or structure
  changed) or *fixed deviation* (a known deviation of the source from its
  contract was corrected, with a test that rejects it); a short note follows
  and names any known deviation that is kept as a limitation.
- **Tests not carried over**: tests of the source that were not taken over,
  one per line, each with the reason.

Ported code is tested again in this repository. Tests, proofs and results of
the earlier implementation are not evidence for kalyx.

| Module | Source | Change | Tests not carried over |
| --- | --- | --- | --- |
| `src/error.rs`, with its tests in `tests/errors.rs` | `cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/error.rs`<br>`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:tests/core/errors.rs` | Adapted. `Bounded<T>` is renamed `Settled<T>`: `Complete(T)` becomes `Value(T)`, `IterationLimit` becomes `State(MathState)` with five states, and the accessors are `value`, `into_value`, `state`, `is_value` and `is_state`. The 25 error kinds become three request kinds and `Fault(FaultKind)` with seven foundation faults, as the [contract](docs/components/errors/contract.md#kinds-of-the-earlier-implementation) maps them. `Error` and `Span` get private fields and accessors, and `Error` no longer implements `PartialEq` or `Eq`. The internal `Halt::IterationLimit(Cap)` becomes `Halt::Stop(MathState, Cap)`, and the two caps of the source, which belong to features kalyx does not have yet, are replaced by the general `Cap::IterationBound`. Deviations fixed: `Error::new` could build a request failure that compared equal to the context's own, and now takes only a `FaultKind` (the `compile_fail,E0308` documentation test of `Error::new` rejects it); the exceeded limit was named only in the message text, and is now the structured `LimitExceeded` (`resource_limits_carry_structured_identifiers`, `frame_and_temporary_limits_differ_by_scope`, `a_request_parameter_limit_names_the_parameter`); an undecided outcome was an `Indeterminate` error, and is now `MathState::Undecided`, with no error kind for a state (`each_math_state_settles_into_a_state`). The four unit tests of the source and two tests of `tests/core/errors.rs` (`ex6_code_outside_the_library_constructs_its_own_errors` and `errors_implement_the_standard_error_trait`) are carried over; their assertions of the text of error messages and of whole errors compared with `==`, including the comparison of a constructed `ResourceLimit` error with the context's and of a constructed `Syntax` error with the parser's, are dropped, since tests compare kind, span and exceeded limit instead. `caps_have_fixed_messages` asserts the fixed text of the general cap in place of the two texts of the source. | `tests/core/errors.rs` `ex1_a_syntax_error_names_its_byte_range`: needs the parser; the tests of the parser will cover the spans of syntax errors.<br>`tests/core/errors.rs` `ex2_incomplete_input_has_an_empty_span_at_the_end`: needs the parser; the tests of the parser will cover the empty span at the end of incomplete input.<br>`tests/core/errors.rs` `ex3_evaluation_errors_carry_the_failing_operation`: needs the parser and evaluation; the tests of the term core and the command entry will cover the span of a division by zero.<br>`tests/core/errors.rs` `ex4_request_level_failures_have_no_span`: needs the request context and the parser; the tests of the context will cover the request failures of a charge, and `request_failures_are_errors_of_the_context_class` already checks that a request failure carries the span its caller gave.<br>`tests/core/errors.rs` `ex5_the_command_line_maps_outcomes_to_exit_statuses`: needs the command-line program; the tests of the command entry and the program will cover exit statuses.<br>`tests/core/errors.rs` `spans_are_char_boundaries_within_the_source`: needs the parser; the tests of the parser will cover span boundaries. |
