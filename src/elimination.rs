//! The elimination skeleton: Gauss–Jordan elimination of the rows of a
//! matrix over a coefficient field whose zero test answers zero, nonzero or
//! undecided.
//!
//! The skeleton is generic over a field, which tests entries for zero and
//! divides, multiplies and subtracts them, and over a storage of rows, which
//! holds the entries and the checks and charges of its domain. The skeleton
//! fixes the control flow and nothing else: it never constructs an error and
//! never charges the request context itself. Every check, charge and error
//! comes from the field or from a hook of the storage, called where the
//! domain's elimination performs it, so the results, errors and work of a
//! reduction depend only on the field and the storage. The storage and its
//! reservation belong to the caller; the skeleton holds no frame and no
//! reservation of the context.
//!
//! Only an entry whose zero test answered nonzero becomes a pivot: the first
//! such candidate at or below the current row, in row order. Candidates that
//! answered zero or undecided are passed over. A column whose candidates
//! answered zero has no pivot; a column whose candidates answered zero or
//! undecided, at least one of them undecided, ends the reduction with the
//! result state `Reduction::Undecided`, because whether the column has a
//! pivot is not known. An entry of another row that answered undecided is
//! eliminated like a nonzero one, which is correct whether it is zero or
//! not. A field that always decides names the uninhabited
//! [`Infallible`] as its reason, so its reductions complete by construction
//! and `complete` unwraps them without a failure path.
//!
//! The module is crate-internal. The rules of this module are stated in the
//! component contract, `docs/components/elimination/contract.md`.

#![cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "the elimination skeleton has no production caller yet; its unit tests run every path"
    )
)]

use std::convert::Infallible;

use crate::coefficient::{CoefficientField, ZeroTest};
use crate::{Context, Result};

#[cfg(test)]
mod tests;

/// The outcome of a reduction.
#[cfg_attr(test, derive(Debug, PartialEq))]
pub(crate) enum Reduction<U> {
    /// The reduction finished, with its pivot columns in increasing order.
    Complete(Vec<usize>),
    /// The candidates of a column answered zero or undecided, at least one of
    /// them undecided, so whether the column has a pivot is not known. The
    /// reason is that of the first candidate that answered undecided. The
    /// storage keeps the state that the reduction reached, with the pivots of
    /// the earlier columns in place.
    ///
    /// This state refines [`MathState::Undecided`](crate::MathState::Undecided).
    /// It carries the reason alone, because no production caller reads it
    /// yet; the first that does adds the undecided column and the pivot
    /// columns found before it.
    Undecided(U),
}

/// The pivot columns of a reduction over a field that always decides.
pub(crate) fn complete(reduction: Reduction<Infallible>) -> Vec<usize> {
    match reduction {
        Reduction::Complete(pivots) => pivots,
        Reduction::Undecided(never) => match never {},
    }
}

/// The rows of a matrix under elimination, with the checks and charges of
/// their domain.
///
/// The entries form `rows()` rows of `width()` columns. The reduction pivots
/// in the first `variables` columns; the columns after them, such as the
/// right-hand sides of a system, are transformed with the rows. The hooks
/// perform the checks and charges of one step of the reduction; the skeleton
/// calls them in the order given here. The storage belongs to the caller,
/// which reserves its room in the context before the reduction and releases
/// it afterwards.
pub(crate) trait EliminationRows {
    type Element;

    /// The number of rows.
    fn rows(&self) -> usize;

    /// The number of columns, including those after the variables.
    fn width(&self) -> usize;

    /// The entry in `row` and `column`, borrowed from the storage.
    fn entry(&self, row: usize, column: usize) -> &Self::Element;

    /// The entry checks of a reduction in the first `variables` columns, and
    /// the empty list that receives the pivot columns.
    fn begin_reduction(&mut self, variables: usize, context: &mut Context) -> Result<Vec<usize>>;

    /// The charge of a pivot candidate, before its zero test.
    fn candidate_step(&self, context: &mut Context) -> Result<()>;

    /// Swaps the entries of `row` and `other` in `column`, with its charge;
    /// a swap of two rows calls it for every column in order.
    fn swap_cell(
        &mut self,
        row: usize,
        other: usize,
        column: usize,
        context: &mut Context,
    ) -> Result<()>;

    /// The checks of the pivot in `row` and `column`, after its row was
    /// swapped into place when `swapped` holds, and the pivot itself.
    fn begin_pivot(
        &mut self,
        row: usize,
        column: usize,
        swapped: bool,
        context: &mut Context,
    ) -> Result<Self::Element>;

    /// Replaces the entry in `row` and `column`, enforcing the request
    /// limits. After a failure the storage is discarded.
    fn store(
        &mut self,
        row: usize,
        column: usize,
        value: Self::Element,
        context: &mut Context,
    ) -> Result<()>;

    /// The first row that the pivot in `row` eliminates from; the rows from
    /// it to the last, except `row` itself, are eliminated.
    fn first_target(&self, row: usize) -> usize;

    /// The charge of a row to eliminate from, before its zero test; it is
    /// charged for the pivot row too when that row lies in the range.
    fn target_step(&self, context: &mut Context) -> Result<()>;

    /// The work after the pivot in `row` and `column` was eliminated from the
    /// other rows.
    fn end_pivot(&mut self, row: usize, column: usize, context: &mut Context) -> Result<()>;

    /// The checks and the room for one more pivot column in `pivots`, which
    /// the skeleton then appends.
    fn reserve_pivot(&mut self, pivots: &mut Vec<usize>, context: &mut Context) -> Result<()>;

    /// The checks after the last column.
    fn end_reduction(&mut self, context: &mut Context) -> Result<()>;
}

/// Reduces `rows` in its first `variables` columns over `field`: after a
/// complete reduction the pivot rows come first, each pivot is one and the
/// other entries of a pivot column are zero in the rows that the storage
/// eliminates from.
pub(crate) fn reduce<F, S>(
    field: &F,
    rows: &mut S,
    variables: usize,
    context: &mut Context,
) -> Result<Reduction<F::Undecided>>
where
    F: CoefficientField,
    S: EliminationRows<Element = F::Element>,
{
    let pivots = rows.begin_reduction(variables, context)?;
    reduce_columns(field, rows, variables, pivots, context)
}

/// The columns of a reduction, until the variables or the rows run out.
fn reduce_columns<F, S>(
    field: &F,
    rows: &mut S,
    variables: usize,
    pivots: Vec<usize>,
    context: &mut Context,
) -> Result<Reduction<F::Undecided>>
where
    F: CoefficientField,
    S: EliminationRows<Element = F::Element>,
{
    let mut pivots = pivots;
    let mut column = 0;
    while column < variables && pivots.len() < rows.rows() {
        let row = pivots.len();
        match find_pivot(field, rows, row, column, context)? {
            (ZeroTest::Nonzero, selected) => {
                pivot_step(field, rows, row, selected, column, &mut pivots, context)?
            }
            (ZeroTest::Zero, _) => {}
            (ZeroTest::Undecided(reason), _) => return Ok(Reduction::Undecided(reason)),
        }
        column += 1;
    }
    rows.end_reduction(context)?;
    Ok(Reduction::Complete(pivots))
}

/// The answer of the candidates of `column` at or below `row`: nonzero with
/// the first candidate that answered nonzero, zero when every candidate
/// answered zero, and otherwise undecided with the reason of the first
/// candidate that answered undecided. The search stops at the first nonzero
/// answer.
fn find_pivot<F, S>(
    field: &F,
    rows: &S,
    row: usize,
    column: usize,
    context: &mut Context,
) -> Result<(ZeroTest<F::Undecided>, usize)>
where
    F: CoefficientField,
    S: EliminationRows<Element = F::Element>,
{
    let mut answer = ZeroTest::Zero;
    let mut candidate = row;
    while candidate < rows.rows() {
        rows.candidate_step(context)?;
        match field.zero_test(rows.entry(candidate, column), context)? {
            ZeroTest::Nonzero => return Ok((ZeroTest::Nonzero, candidate)),
            ZeroTest::Zero => {}
            ZeroTest::Undecided(reason) => answer = first_undecided(answer, reason),
        }
        candidate += 1;
    }
    Ok((answer, candidate))
}

/// The answer of a column after a candidate answered undecided with
/// `reason`: the first undecided answer is kept.
fn first_undecided<U>(answer: ZeroTest<U>, reason: U) -> ZeroTest<U> {
    match answer {
        ZeroTest::Zero => ZeroTest::Undecided(reason),
        kept => kept,
    }
}

/// One pivot: the swap of its row into place, the checks of the pivot, the
/// normalization of the pivot row, the elimination from the other rows and
/// the new pivot column.
fn pivot_step<F, S>(
    field: &F,
    rows: &mut S,
    row: usize,
    selected: usize,
    column: usize,
    pivots: &mut Vec<usize>,
    context: &mut Context,
) -> Result<()>
where
    F: CoefficientField,
    S: EliminationRows<Element = F::Element>,
{
    let swapped = selected != row;
    if swapped {
        swap_rows(rows, row, selected, context)?;
    }
    let pivot = rows.begin_pivot(row, column, swapped, context)?;
    normalize_row(field, rows, row, column, &pivot, context)?;
    eliminate_rows(field, rows, row, column, context)?;
    rows.end_pivot(row, column, context)?;
    rows.reserve_pivot(pivots, context)?;
    pivots.push(column);
    Ok(())
}

/// Swaps `row` and `other`, column by column.
fn swap_rows<S: EliminationRows>(
    rows: &mut S,
    row: usize,
    other: usize,
    context: &mut Context,
) -> Result<()> {
    let mut column = 0;
    while column < rows.width() {
        rows.swap_cell(row, other, column, context)?;
        column += 1;
    }
    Ok(())
}

/// Divides the entries of `row` from `column` on by the pivot.
fn normalize_row<F, S>(
    field: &F,
    rows: &mut S,
    row: usize,
    column: usize,
    pivot: &F::Element,
    context: &mut Context,
) -> Result<()>
where
    F: CoefficientField,
    S: EliminationRows<Element = F::Element>,
{
    let mut c = column;
    while c < rows.width() {
        let value = field.divide(rows.entry(row, c), pivot, context)?;
        rows.store(row, c, value, context)?;
        c += 1;
    }
    Ok(())
}

/// Eliminates the pivot in `row` and `column` from the rows that the storage
/// names.
fn eliminate_rows<F, S>(
    field: &F,
    rows: &mut S,
    row: usize,
    column: usize,
    context: &mut Context,
) -> Result<()>
where
    F: CoefficientField,
    S: EliminationRows<Element = F::Element>,
{
    let mut other = rows.first_target(row);
    while other < rows.rows() {
        rows.target_step(context)?;
        if other != row {
            eliminate_row(field, rows, row, other, column, context)?;
        }
        other += 1;
    }
    Ok(())
}

/// Eliminates the pivot in `row` and `column` from `other`, unless the entry
/// of `other` in the pivot column answered zero.
fn eliminate_row<F, S>(
    field: &F,
    rows: &mut S,
    row: usize,
    other: usize,
    column: usize,
    context: &mut Context,
) -> Result<()>
where
    F: CoefficientField,
    S: EliminationRows<Element = F::Element>,
{
    match field.zero_test(rows.entry(other, column), context)? {
        ZeroTest::Zero => Ok(()),
        ZeroTest::Nonzero | ZeroTest::Undecided(_) => {
            let factor = rows.entry(other, column).clone();
            subtract_row(field, rows, row, other, column, &factor, context)
        }
    }
}

/// Subtracts `factor` times `row` from `other`, from `column` on.
fn subtract_row<F, S>(
    field: &F,
    rows: &mut S,
    row: usize,
    other: usize,
    column: usize,
    factor: &F::Element,
    context: &mut Context,
) -> Result<()>
where
    F: CoefficientField,
    S: EliminationRows<Element = F::Element>,
{
    let mut c = column;
    while c < rows.width() {
        let product = field.multiply(factor, rows.entry(row, c), context)?;
        let value = field.subtract(rows.entry(other, c), &product, context)?;
        rows.store(other, c, value, context)?;
        c += 1;
    }
    Ok(())
}
