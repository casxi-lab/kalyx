# Shared result types

This contract states the shared result types of kalyx that exist today:
`Evidence`, the evidence of a decision, and `Truth`, a three-valued truth
value. It states their values, their operations and their tests, and
applies to the types in `src/shared.rs` and to every function of the library
that returns them. The
[architecture](../../architecture.md#shared-result-types) places the
component among the foundations, and the
[public API conventions](../../conventions/public-api.md) state the rules
that every public interface follows; conventions
[2](../../conventions/public-api.md#2-errors-separate-from-result-states),
[3](../../conventions/public-api.md#3-extensible-enums-and-records) and
[14](../../conventions/public-api.md#14-canonical-representation-and-equality)
concern these types and are not restated here. The mathematical states of
`MathState` belong to the [errors and result states](../errors/contract.md).

**Status.** Implemented in `src/shared.rs`, at tier A1 (tested with a written
contract). The types are written anew for kalyx; the earlier implementation
served only as a reference, so [PORTING](../../../PORTING.md) has no row for
them. No public entry of the library other than their own three operations
returns either type yet: their first production caller is to be the
assumption queries of function expressions, planned for release 0.2, and no
entry of that release produces numerical evidence except by combining
evidence that is already numerical. The unit tests of `src/shared.rs` and
the tests in `tests/shared_results.rs` produce every variant through the
operations. The other shared result types of the architecture,
`Completeness` and `Guarantee`, are planned and not part of this contract
yet.

## Interface

The crate root re-exports both types. They are defined once, in the private
module `src/shared.rs`, so they have no other path:

- `Evidence`, with the variants `Proved`, `Refuted`, `NumericEvidence` and
  `Unknown`, and the methods `and(self, other: Evidence) -> Evidence` and
  `truth(self) -> Truth`;
- `Truth`, with the variants `True`, `False` and `Unknown`, and the method
  `and(self, other: Truth) -> Truth`.

Both types are `#[non_exhaustive]` and derive `Clone`, `Copy`, `Debug`,
`PartialEq`, `Eq` and `Hash`, as `MathState` does. They implement no other
trait: no `Default`, no `Display`, no order, no operator such as `!` or `&`
and no conversion trait such as `From`. The three methods are `const fn`s
that take their operands by value and return the result itself, not a
`Result`.

## Rules

### Values

- **Evidence.** `Proved`: the proposition is proved. `Refuted`: its negation
  is proved. `NumericEvidence`: the proposition holds numerically, which is
  evidence, not a proof. `Unknown`: there is no evidence either way. `Proved`
  and `Refuted` decide the proposition; the other two do not.
- **Truth.** `True` and `False` are reliable. `Unknown` says that the truth
  value was not decided and carries no information about which of the other
  two holds.
- **States are values.** An `Evidence` or a `Truth` is part of an answer,
  inside `Ok`, and never stands for a request failure: no `ErrorKind` stands
  for one of them, neither converts into an `Error`, and neither is a
  `MathState`. A question that the library cannot decide is answered with
  `Unknown`; a request that has no answer fails with an `Error`, as every
  request does.
- **One definition.** No component defines a synonym of either type: a
  component that needs evidence or a three-valued truth value uses these
  types, and a later release extends them with variants or methods. Variant
  names are never renamed or reused.

### Combinations

The types have these three operations:

| Operation | Result |
| --- | --- |
| `Evidence::and` | `Refuted` if either operand is `Refuted`; otherwise `Unknown` if either is `Unknown`; otherwise `NumericEvidence` if either is `NumericEvidence`; otherwise, both operands being `Proved`, `Proved` |
| `Evidence::truth` | `True` for `Proved`, `False` for `Refuted`, and `Unknown` for `NumericEvidence` and for `Unknown` |
| `Truth::and` | the strong Kleene conjunction: `False` if either operand is `False`; otherwise `Unknown` if either is `Unknown`; otherwise `True` |

- **Combining never raises the evidence.** A conjunction is never stronger
  than the weakest evidence that it needs. It is `Proved` exactly when both
  operands are `Proved`. One `Refuted` operand decides the conjunction on its
  own, as `False` decides a strong Kleene conjunction, so the conjunction is
  `Refuted` exactly when an operand is `Refuted`. The truth value of a
  conjunction of evidence is therefore the conjunction of the truth values
  of its operands: `a.and(b).truth()` equals `a.truth().and(b.truth())` for
  every `a` and `b`. `Truth::and` and `Evidence::and` do not follow
  [convention 17](../../conventions/public-api.md#17-no-implicit-conventions):
  they state the strong Kleene conjunction, and the conjunction of evidence
  that agrees with it, only in their documentation, and their results do not
  name it.
- **Numerical evidence is never a proof.** `NumericEvidence` never becomes
  `Proved` or `True`: its truth value is `Unknown`, and its conjunction with
  any evidence is `NumericEvidence`, `Unknown` or `Refuted`.
- **Three-valued equality.** A truth value that is decided component by
  component, such as the equality of two collections compared element by
  element, is the conjunction of the truth values of its components, folded
  with `Truth::and` from `True`, as the collections of the earlier
  implementation fold it
  (`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/environment/collection/tree.rs:345-380`).
  The component that brings a three-valued equality follows this rule and
  refers to it here; no three-valued equality exists yet. So an `Unknown`
  from a three-valued equality is never promoted: one `Unknown` component
  without a `False` one keeps the equality `Unknown`.
- **Not charged.** Building a value and the three operations take no
  context, allocate nothing and charge nothing. They have no charge point,
  so the limits, the deadline and cancellation of a request do not apply to
  them.

### The reason of an undecided zero test

A coefficient field whose zero test cannot always decide names its reason
as the associated type `Undecided` of the
[coefficient-field trait](../../architecture.md#coefficient-field-trait).
For a field that is not exact, such as a field of numerical
approximations, the reason is `Evidence`, and its zero test gives
`ZeroTest::Undecided` only with `NumericEvidence` or `Unknown`: a `Proved`
or a `Refuted` decides the test, which then gives `Zero` or `Nonzero`. Every
coefficient field of the library is exact so far and always decides, with
the reason `std::convert::Infallible`.

## Requirements

The shared result types had no requirement identifiers in the earlier
implementation, which had no shared evidence type, so the requirements of
this component are named after what they state. Tests are in
`tests/shared_results.rs` unless the entry names `src/shared.rs`,
`tests/root_names.rs` or a documentation test.

### Defined once, extensible

`Evidence` and `Truth` are each defined once, at the crate root, and are
`#[non_exhaustive]`.

- **Implemented here.** The private module `src/shared.rs`, the re-export in
  `src/lib.rs` and the two names in `api/root-names.txt`.
- **Tests.** The `compile_fail,E0004` documentation tests of `Evidence` and
  `Truth`, in which code outside the library matches the variants without a
  wildcard arm and fails to compile, and
  `the_crate_root_has_exactly_the_listed_public_names` in
  `tests/root_names.rs`.

### Every variant is produced

Each of the seven variants has a test that produces it through an
operation.

- **Implemented here.** The three operations in `src/shared.rs`.
- **Tests.** `each_evidence_comes_out_of_a_conjunction` gives all four kinds
  of evidence from `Evidence::and`, and `each_truth_comes_out_of_evidence`
  all three truth values from `Evidence::truth`, both in `src/shared.rs`.
  No entry produces numerical evidence yet except by combining evidence that
  is already numerical, so the unit test gives `NumericEvidence` to the
  conjunction as an operand, as the unit tests of the errors produce each
  `MathState`.

### Combining never raises the evidence

- **Implemented here.** `Evidence::and` and `Evidence::truth`.
- **Tests.** Negative: `combining_evidence_never_raises_its_level`, over all
  16 pairs of evidence: the conjunction is `Proved` exactly when both operands
  are, `Refuted` exactly when one is, and its truth value is the conjunction
  of the truth values of its operands. Each pair, in either order, also gives
  the conjunction that the rule of the [combinations](#combinations) table
  gives, computed in the test apart from `Evidence::and`, so the test fixes
  all 16 results and neither `Unknown` nor `NumericEvidence` turns into the
  other.

### Numerical evidence is never a proof

- **Implemented here.** `Evidence::truth` and `Evidence::and`.
- **Tests.** Negative: `numerical_evidence_never_becomes_proved_or_true`:
  the truth value of `NumericEvidence` is `Unknown`, and its conjunction with
  each of the four kinds of evidence, on either side, is neither `Proved` nor
  `True`.

### An unknown from a three-valued equality is never promoted

- **Implemented here.** `Truth::and`, with the rule for three-valued
  equality above.
- **Tests.** Negative: `an_unknown_from_three_valued_equality_is_never_promoted`:
  the components `True`, `Unknown` and `True` fold into `Unknown`, and the
  conjunction of `Unknown` with `True` or with `Unknown` is `Unknown`.

## Testing obligations

1. **Variants.** For each type, one test that produces each of its variants.
2. **Extensible enums.** For each type, one `compile_fail,E0004`
   documentation test.
3. **Combinations.** The three negative tests of the requirements above, the
   first of them over all pairs of evidence.
4. **Names of the crate root.** The two names are in `api/root-names.txt`,
   which `tests/root_names.rs` compares with the crate root.

## Extractability

The component is at tier A1 with no upgrade to A3 planned and is not a proof
target, so it has no entry in a module list and the provable subset of Rust
is not required of it. Its code is written in that style nonetheless: each
method is one `match` on operands taken by value, with no loop, closure,
function value, borrow, allocation or `?`. None of it has been extracted.

## Current deviations

None: the code and the tests follow every rule above.
