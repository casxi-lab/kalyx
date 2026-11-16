# Elimination skeleton

This contract states the elimination skeleton of kalyx: Gauss–Jordan
elimination of the rows of a matrix over a coefficient field whose zero test
answers zero, nonzero or undecided, generic over the field and over a
storage of rows. It applies to the module `src/elimination.rs`, with its
tests in `src/elimination/tests.rs` and the test fields that they use in
`src/coefficient/test_fields.rs`. The
[architecture](../../architecture.md#later-foundations) lists the component
among the foundations of release 0.2. The coefficient traits and their zero
test belong to the [exact numbers](../numbers/contract.md#the-coefficient-field-trait),
the charges and reservations to the [context](../context/contract.md), and
the errors and the result states to the
[errors and result states](../errors/contract.md).

**Status.** Implemented in `src/elimination.rs`, at tier A1 (tested with a
written contract), with no tier above A1 planned. The skeleton is a
crate-internal module: it has no public interface, and the public names of
the crate root do not change. It is ported from the elimination skeleton of
the earlier implementation, as [PORTING](../../../PORTING.md) records. No
code outside the module calls it yet: its first production caller is
planned to be the null space computation of the Berlekamp factorization
over the prime fields, in release 0.2. Until then the module expects the
`dead_code` lint outside its tests.

## Scope

- **Included.** The reduction of the first `variables` columns of a matrix
  over a field bounded by `CoefficientField`, with the columns after them
  transformed with the rows; the choice of pivots by the three answers of
  the zero test; the hooks of the storage and their order; the complete and
  the undecided result of a reduction.
- **Planned.** The first production caller, the null space of the
  Berlekamp factorization; the undecided column and the pivot columns found
  before it, which the first caller that reads an undecided reduction adds
  to the state.
- **Excluded.** Fraction-free elimination over rings that are not fields,
  and the operations of matrices, are planned for release 0.4. The skeleton
  holds no matrix type: the storage of the caller holds the entries.

## Interface

The module is declared as `mod elimination;` in `src/lib.rs`, and its items
are `pub(crate)`:

- `Reduction<U>`, the outcome of a reduction: `Complete(Vec<usize>)`, with
  the pivot columns in increasing order, or `Undecided(U)`, with the reason
  of the zero test that left a column undecided.
- `complete(reduction: Reduction<Infallible>) -> Vec<usize>`, the pivot
  columns of a reduction over a field that always decides.
- `EliminationRows`, the trait of a storage of rows, with its type
  `Element` and the hooks of [the storage](#the-storage).
- `reduce(field, rows, variables, context)`, generic over `F:
  CoefficientField` and `S: EliminationRows<Element = F::Element>`, which
  returns `Result<Reduction<F::Undecided>>`.

## Rules

### Zero tests and pivots

- **Answers.** The zero test of the field answers `Zero`, `Nonzero` or
  `Undecided` with a reason (`ZeroTest` of the coefficient traits). Zero
  means that the element is zero and nonzero that it is not; undecided
  carries no information about the element.
- **Pivots.** Only an entry whose test answered nonzero becomes a pivot.
  An entry that answered zero is passed over as zero. An entry that
  answered undecided is neither a pivot nor treated as zero; a result that
  depends on it is the undecided state, never a rank or a singular matrix.
- **Pivot order.** The pivot of a column is the first candidate at or below
  the current row, in row order, whose test answered nonzero. The search
  stops there; a candidate that answered undecided before it is passed
  over.
- **Undecided columns.** A column whose candidates answered zero or
  undecided, at least one of them undecided, is undecided: whether it has a
  pivot is not known, so the reduction stops there with
  `Reduction::Undecided` and the reason of the first undecided answer of
  that column. A column whose candidates all answered zero has no pivot,
  and the reduction moves on to the next column with the same row.
- **Elimination of an undecided entry.** An entry of another row that
  answered undecided is eliminated like a nonzero one, with itself as the
  factor, which is correct whether it is zero or not. An entry that
  answered zero is left as it is.

### Control flow

For each of the first `variables` columns, while rows remain, the search
tests the candidates at or below the current row. The row of the pivot that
it finds is swapped into place cell by cell, unless it is the current row;
the pivot row is divided by the pivot from the pivot column on, and the
pivot is eliminated from the rows that the storage names, except the pivot
row, by subtracting the entry of each row in the pivot column times the
pivot row, from the pivot column on. The column is then appended to the
pivot columns, and the reduction moves on with the next column and the next
row. After a complete reduction the pivot rows come first, each pivot is
one, and the other entries of a pivot column are zero in the rows that the
storage eliminates from.

### The storage

The storage holds the entries, `rows()` rows of `width()` columns borrowed
through `entry`, and performs the checks and charges of its domain in hooks
that the skeleton calls in this order: `begin_reduction`, the entry checks
of a reduction, which returns the list that receives the pivot columns;
`candidate_step` before the zero test of each candidate; `swap_cell` for
every column of a swap; `begin_pivot`, the checks of a pivot, which returns
it; `store`, the replacement of an entry with its limits, after which a
failed storage is discarded; `first_target`, the first row to eliminate
from; `target_step` before each such row, the pivot row included when it is
in the range; `end_pivot`; `reserve_pivot`, the room for one more pivot
column; and `end_reduction` after the last column.

- **Hooks.** The skeleton never constructs an error and never charges the
  context itself; every check, charge and error comes from the field or the
  storage, so the results, errors and work of a reduction depend only on
  them. A hook or a field operation that fails ends the reduction with its
  error, and no further hook runs.
- **Ownership.** The storage and its reservation belong to the caller,
  which reserves the room of the entries in the context before the
  reduction and releases it afterwards. The skeleton opens no frame and
  holds no reservation.

### The undecided state

`Reduction::Undecided` refines `MathState::Undecided`: a reduction that
depends on an undecided zero test ends in it, inside `Ok`, as the
[shared result types](../../architecture.md#shared-result-types) state for
a status type of a feature. The storage keeps the state that the reduction
reached, with the pivots of the earlier columns in place, and no hook runs
after the search of the undecided column. The state carries the reason
alone, because no production field answers undecided yet. Over a field
whose reason type is `Infallible`, such as the prime fields, a reduction
completes by construction, and `complete` unwraps its pivot columns without
a failure path.

## Testing obligations

The tests are in `src/elimination/tests.rs`. The test fields of residues
modulo a prime, `UndecidedResidues`, which answers undecided for the values
of a chosen set and reports every zero test, and `ExactResidues`, which
always decides, charge nothing.

1. **Reduced row echelon form.** Generated reductions over fields with and
   without undecided answers are the reduced row echelon forms of their
   inputs, checked against ranks and a factorization computed
   independently: `exact_reductions_are_reduced_row_echelon_forms` and
   `undecided_answers_never_become_pivots`; forward elimination gives the
   determinant: `forward_elimination_yields_the_determinant`.
2. **Undecided answers.** `undecided_candidates_are_passed_over`,
   `undecided_columns_end_the_reduction` (the undecided state) and
   `undecided_answers_never_become_pivots`.
3. **Hooks and ownership.** `the_skeleton_never_charges`,
   `a_failing_hook_ends_the_reduction` and
   `the_skeleton_holds_no_frame_and_no_reservation`.
4. **Control flow, step by step.**
   `the_search_stops_at_the_first_nonzero_answer`,
   `the_search_passes_over_a_zero_answer`,
   `the_search_passes_over_an_undecided_answer_and_remembers_the_first`,
   `after_the_last_candidate_the_search_returns_the_answer_of_the_column`,
   `the_first_undecided_answer_replaces_zero`,
   `a_later_undecided_answer_keeps_the_first_reason`,
   `a_column_that_answered_zero_is_passed_over`,
   `an_undecided_column_ends_the_reduction_without_a_hook`,
   `an_undecided_entry_of_another_row_is_eliminated`,
   `a_reduction_over_a_field_that_always_decides_unwraps`,
   `a_column_that_answered_nonzero_runs_the_pivot_step`,
   `a_pivot_in_the_current_row_stays_in_place`,
   `normalization_divides_the_pivot_row_entry_by_entry`,
   `the_elimination_passes_over_the_pivot_row`,
   `the_elimination_eliminates_from_every_other_row`,
   `a_zero_entry_of_another_row_is_left_as_it_is`,
   `a_nonzero_entry_of_another_row_is_eliminated`,
   `row_subtraction_replaces_each_entry_by_its_difference` and
   `a_single_undecided_entry_gives_an_undecided_reduction`.
5. **Prime fields.** Over the prime fields of the library, 1,000 generated
   reductions agree with a naive elimination written in the test:
   `reductions_over_prime_fields_match_naive_elimination`.
6. **Resources, cancellation and rollback.** The representative operation is
   a reduction over a prime field with a storage that charges one unit in
   every hook that takes the context, and a reservation of its entries by
   the caller.
   `an_elimination_over_a_prime_field_passes_at_the_exact_work_and_fails_one_unit_below`,
   `an_elimination_over_a_prime_field_passes_at_the_exact_storage_and_fails_one_byte_below`,
   `cancellation_at_every_charge_of_an_elimination_is_reported`,
   `a_failed_or_cancelled_elimination_keeps_its_input_and_the_retained_storage`
   and `random_eliminations_over_prime_fields_do_not_panic`. The skeleton
   has no recursion.

## Extractability

No proof target is registered for the skeleton, and its files are not in
the module list of [formal verification](../../formal-verification.md#module-list).
It keeps the shape in which the earlier implementation extracted it: one
loop per function, each an index loop whose condition is a comparison; the
result state returned from inside the column loop; the uninhabited reason
unwrapped by an empty `match`; no closure and no `cfg` but `#[cfg(test)]`
on the test module, with the lint expectation of the module selected by
`cfg_attr`. The tests use `RefCell` and closures; they are test code.

## Current deviations

None: the code and the tests follow every rule above.
