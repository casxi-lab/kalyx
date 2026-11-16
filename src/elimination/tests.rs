//! Properties of the elimination skeleton over test-only fields and storage.
//!
//! The fields are the test fields of residues modulo a prime $p$ in
//! `crate::coefficient::test_fields`: one whose zero test answers undecided
//! for the values of a chosen set, which may contain zero, and decides every
//! other value, and one that always decides; neither charges. The storage
//! `Grid` holds the entries in row-major order, charges nothing, and records
//! every hook and every zero test in a log. The checks judge the results by
//! the definition of the reduced row echelon form, by a factorization of the
//! input through the result, and by ranks and determinants that the tests
//! compute independently from minors, by cofactor expansion modulo $p$.
//!
//! - A complete reduction is the reduced row echelon form of its input, with
//!   or without undecided answers, since that form is unique.
//! - Every pivot answered nonzero, as the last of the zero tests of its
//!   search, and every earlier test of the search answered zero or
//!   undecided: an entry that answered undecided never becomes a pivot.
//! - A reduction is undecided exactly when the tests of a search answered
//!   zero or undecided and at least one of them undecided; its reason is the
//!   first undecided answer of that search, and no hook runs after the
//!   search.
//! - An entry of another row that answered undecided is eliminated.
//! - The skeleton never charges, never constructs an error and holds no
//!   frame or reservation: a reduction with storage and field that do not
//!   charge runs under an exhausted budget and a cancelled flag, a failing
//!   hook ends the reduction with its error before any further hook runs,
//!   and every hook sees the frames and the reservations of its caller.
//!
//! The tests of the control flow restate, one by one, the properties that
//! the qualification case `elimination-skeleton` of the earlier
//! implementation proved. Over the prime fields of the library the skeleton
//! agrees with a naive elimination written here, and the resource tests run
//! it with a storage that charges one unit per hook, as a caller does.

use std::cell::RefCell;
use std::convert::Infallible;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use super::{
    EliminationRows, Reduction, complete, eliminate_row, eliminate_rows, find_pivot,
    first_undecided, normalize_row, pivot_step, reduce, reduce_columns, subtract_row,
};
use crate::coefficient::test_fields::{ExactResidues, UndecidedResidues, residue_product};
use crate::coefficient::{CoefficientRing, PrimeField, PrimeResidue, ZeroTest};
use crate::context::{CancelFlag, CancelProbe, Clock, Storage};
use crate::number::Integer;
use crate::{Context, Error, ErrorKind, FaultKind, LimitField, LimitId, Limits, Result};

// ---------------------------------------------------------------------------
// Test support

/// A fixed linear congruential sequence for reproducible generated inputs.
///
/// When a test panics while a sequence is alive, the sequence reports its
/// seed and how many values it produced, which identify the generated case
/// that failed.
struct Sequence {
    seed: u64,
    state: u64,
    drawn: u64,
}

impl Sequence {
    fn new(seed: u64) -> Self {
        Self {
            seed,
            state: seed,
            drawn: 0,
        }
    }

    /// The next value, uniformly in `low..=high` up to the generator's bias.
    fn next_in(&mut self, low: i64, high: i64) -> i64 {
        self.state = self
            .state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.drawn += 1;
        let span = (high - low + 1) as u64;
        low + ((self.state >> 33) % span) as i64
    }

    /// One of `items`, which must not be empty.
    fn pick<'a, T>(&mut self, items: &'a [T]) -> &'a T {
        &items[self.next_in(0, items.len() as i64 - 1) as usize]
    }
}

impl Drop for Sequence {
    fn drop(&mut self) {
        if std::thread::panicking() {
            eprintln!(
                "generated inputs: seed {:#x}, failure after {} values were drawn",
                self.seed, self.drawn
            );
        }
    }
}

/// Runs one generated case; if it panics, reports `label`, the input that
/// reproduces the case, before the panic continues.
fn case(label: impl std::fmt::Display, check: impl FnOnce()) {
    struct Report<L: std::fmt::Display>(L);

    impl<L: std::fmt::Display> Drop for Report<L> {
        fn drop(&mut self) {
            if std::thread::panicking() {
                eprintln!("generated case failed: {}", self.0);
            }
        }
    }

    let _report = Report(label);
    check();
}

/// A context under the default limits.
fn context() -> Context {
    Context::new(Limits::new(), CancelFlag::new())
}

/// What the reduction did, in order.
#[derive(Clone, Debug, PartialEq)]
enum Event {
    Begin,
    Candidate,
    Test(u32, ZeroTest<u32>),
    Swap,
    Pivot {
        row: usize,
        column: usize,
        value: u32,
    },
    Store,
    Target,
    EndPivot,
    Reserve,
    End,
}

type Log = RefCell<Vec<Event>>;

/// The report of a test field that records each zero test in `log`.
fn recorder(log: &Log) -> impl Fn(u32, &ZeroTest<u32>) + '_ {
    move |value, answer| log.borrow_mut().push(Event::Test(value, *answer))
}

/// Entries in row-major order. With `below` set, a pivot eliminates only the
/// rows below it, as a determinant needs. The store numbered `fail_at`, from
/// zero, fails with a syntax error.
struct Grid<'a> {
    rows: usize,
    width: usize,
    entries: Vec<u32>,
    below: bool,
    stores: usize,
    fail_at: Option<usize>,
    log: &'a Log,
}

impl<'a> Grid<'a> {
    fn new(rows: usize, width: usize, entries: &[u32], log: &'a Log) -> Self {
        assert_eq!(entries.len(), rows * width);
        Self {
            rows,
            width,
            entries: entries.to_vec(),
            below: false,
            stores: 0,
            fail_at: None,
            log,
        }
    }

    fn record(&self, event: Event) {
        self.log.borrow_mut().push(event);
    }
}

impl EliminationRows for Grid<'_> {
    type Element = u32;

    fn rows(&self) -> usize {
        self.rows
    }

    fn width(&self) -> usize {
        self.width
    }

    fn entry(&self, row: usize, column: usize) -> &u32 {
        &self.entries[row * self.width + column]
    }

    fn begin_reduction(&mut self, _variables: usize, _context: &mut Context) -> Result<Vec<usize>> {
        self.record(Event::Begin);
        Ok(Vec::new())
    }

    fn candidate_step(&self, _context: &mut Context) -> Result<()> {
        self.record(Event::Candidate);
        Ok(())
    }

    fn swap_cell(
        &mut self,
        row: usize,
        other: usize,
        column: usize,
        _context: &mut Context,
    ) -> Result<()> {
        self.record(Event::Swap);
        self.entries
            .swap(row * self.width + column, other * self.width + column);
        Ok(())
    }

    fn begin_pivot(
        &mut self,
        row: usize,
        column: usize,
        _swapped: bool,
        _context: &mut Context,
    ) -> Result<u32> {
        let value = self.entries[row * self.width + column];
        self.record(Event::Pivot { row, column, value });
        Ok(value)
    }

    fn store(
        &mut self,
        row: usize,
        column: usize,
        value: u32,
        _context: &mut Context,
    ) -> Result<()> {
        self.record(Event::Store);
        if self.fail_at == Some(self.stores) {
            return Err(store_failure());
        }
        self.stores += 1;
        self.entries[row * self.width + column] = value;
        Ok(())
    }

    fn first_target(&self, row: usize) -> usize {
        if self.below { row + 1 } else { 0 }
    }

    fn target_step(&self, _context: &mut Context) -> Result<()> {
        self.record(Event::Target);
        Ok(())
    }

    fn end_pivot(&mut self, _row: usize, _column: usize, _context: &mut Context) -> Result<()> {
        self.record(Event::EndPivot);
        Ok(())
    }

    fn reserve_pivot(&mut self, _pivots: &mut Vec<usize>, _context: &mut Context) -> Result<()> {
        self.record(Event::Reserve);
        Ok(())
    }

    fn end_reduction(&mut self, _context: &mut Context) -> Result<()> {
        self.record(Event::End);
        Ok(())
    }
}

/// The error of a failing store of `Grid`.
fn store_failure() -> Error {
    Error::new(FaultKind::Syntax, None, "store failure")
}

/// The determinant of the square matrix `a` of order `n` modulo `p`, by
/// cofactor expansion along the first row.
fn determinant(a: &[u32], n: usize, p: u32) -> u32 {
    if n == 0 {
        return 1 % p;
    }
    let mut total = 0_u64;
    for column in 0..n {
        let minor: Vec<u32> = (1..n)
            .flat_map(|row| (0..n).filter(move |&c| c != column).map(move |c| (row, c)))
            .map(|(row, c)| a[row * n + c])
            .collect();
        let term = u64::from(a[column]) * u64::from(determinant(&minor, n - 1, p)) % u64::from(p);
        total = if column % 2 == 0 {
            (total + term) % u64::from(p)
        } else {
            (total + u64::from(p) - term) % u64::from(p)
        };
    }
    total as u32
}

/// The subsets of `0..n` with `k` elements, each in increasing order.
fn subsets(n: usize, k: usize) -> Vec<Vec<usize>> {
    if k == 0 {
        return vec![Vec::new()];
    }
    let mut result = Vec::new();
    for last in k - 1..n {
        for mut subset in subsets(last, k - 1) {
            subset.push(last);
            result.push(subset);
        }
    }
    result
}

/// The rank of the `rows` by `columns` matrix `a` modulo `p`: the largest
/// order of a nonzero minor.
fn rank(a: &[u32], rows: usize, columns: usize, p: u32) -> usize {
    for k in (1..=rows.min(columns)).rev() {
        for chosen_rows in subsets(rows, k) {
            for chosen_columns in subsets(columns, k) {
                let minor: Vec<u32> = chosen_rows
                    .iter()
                    .flat_map(|&row| chosen_columns.iter().map(move |&c| a[row * columns + c]))
                    .collect();
                if determinant(&minor, k, p) != 0 {
                    return k;
                }
            }
        }
    }
    0
}

/// Checks that `reduced`, with pivot columns `pivots`, is the reduced row
/// echelon form of `a` modulo `p`: the pivots increase, each is one, the
/// other entries of a pivot column and the entries left of each pivot are
/// zero, the rows after the last pivot are zero, every row of `a` is the
/// combination of the pivot rows with its own entries in the pivot columns
/// as coefficients, and the number of pivots is the rank of `a`.
fn assert_reduced_form(
    a: &[u32],
    reduced: &[u32],
    pivots: &[usize],
    rows: usize,
    columns: usize,
    p: u32,
) {
    assert!(
        pivots.windows(2).all(|pair| pair[0] < pair[1]),
        "{pivots:?}"
    );
    for (k, &pivot) in pivots.iter().enumerate() {
        assert_eq!(reduced[k * columns + pivot], 1, "pivot {k}");
        for row in 0..rows {
            if row != k {
                assert_eq!(
                    reduced[row * columns + pivot],
                    0,
                    "column {pivot}, row {row}"
                );
            }
        }
        for column in 0..pivot {
            assert_eq!(reduced[k * columns + column], 0, "left of pivot {k}");
        }
    }
    assert!(reduced[pivots.len() * columns..].iter().all(|&v| v == 0));
    for row in 0..rows {
        for column in 0..columns {
            let combination = pivots.iter().enumerate().fold(0_u64, |sum, (k, &pivot)| {
                (sum + u64::from(a[row * columns + pivot])
                    * u64::from(reduced[k * columns + column]))
                    % u64::from(p)
            });
            assert_eq!(
                combination,
                u64::from(a[row * columns + column]),
                "row {row}, column {column}"
            );
        }
    }
    assert_eq!(pivots.len(), rank(a, rows, columns, p));
}

/// A matrix with entries modulo `p`, about half of them zero.
fn generated(sequence: &mut Sequence, rows: usize, columns: usize, p: u32) -> Vec<u32> {
    (0..rows * columns)
        .map(|_| {
            if sequence.next_in(0, 1) == 0 {
                0
            } else {
                sequence.next_in(1, i64::from(p) - 1) as u32
            }
        })
        .collect()
}

/// The answers of each pivot search in `log`, and the value of the pivot it
/// chose, if any.
fn searches(log: &[Event]) -> Vec<(Vec<ZeroTest<u32>>, Option<u32>)> {
    let mut result = Vec::new();
    let mut index = 0;
    while index < log.len() {
        if log[index] != Event::Candidate {
            index += 1;
            continue;
        }
        let mut answers = Vec::new();
        while index < log.len() && log[index] == Event::Candidate {
            let Event::Test(_, answer) = &log[index + 1] else {
                panic!("a candidate without a test at {index}");
            };
            answers.push(*answer);
            index += 2;
        }
        while index < log.len() && log[index] == Event::Swap {
            index += 1;
        }
        let pivot = match log.get(index) {
            Some(Event::Pivot { value, .. }) => Some(*value),
            _ => None,
        };
        result.push((answers, pivot));
    }
    result
}

// ---------------------------------------------------------------------------
// The properties of the earlier implementation, ported

/// Over a field that decides every test, each generated reduction is the
/// reduced row echelon form, each pivot is the first candidate that answered
/// nonzero, and the field with the uninhabited reason gives the same result.
#[test]
fn exact_reductions_are_reduced_row_echelon_forms() {
    let p = 7;
    let mut sequence = Sequence::new(0x5eed_e1e0);
    for _ in 0..300 {
        let rows = sequence.next_in(0, 4) as usize;
        let columns = sequence.next_in(0, 4) as usize;
        let a = generated(&mut sequence, rows, columns, p);
        let log = Log::default();
        let mut grid = Grid::new(rows, columns, &a, &log);
        let report = recorder(&log);
        let field = UndecidedResidues {
            p,
            undecided: &[],
            report: &report,
        };
        let reduction = reduce(&field, &mut grid, columns, &mut context()).unwrap();
        let Reduction::Complete(pivots) = reduction else {
            panic!("a field without undecided values answered undecided");
        };
        assert_reduced_form(&a, &grid.entries, &pivots, rows, columns, p);
        let log = log.take();
        assert_eq!(log.first(), Some(&Event::Begin));
        assert_eq!(log.last(), Some(&Event::End));
        for (answers, pivot) in searches(&log) {
            let last = answers.len() - 1;
            assert!(answers[..last].iter().all(|a| *a == ZeroTest::Zero));
            assert_eq!(answers[last] == ZeroTest::Nonzero, pivot.is_some());
            assert_ne!(pivot, Some(0));
        }
        let exact_log = Log::default();
        let mut exact = Grid::new(rows, columns, &a, &exact_log);
        let reduction = reduce(&ExactResidues { p }, &mut exact, columns, &mut context()).unwrap();
        assert_eq!((complete(reduction), exact.entries), (pivots, grid.entries));
    }
}

/// With elimination below each pivot only, the product of the pivots with
/// the sign of the swaps is the determinant, which is zero exactly when a
/// column has no pivot, and the entries below each pivot are zero.
#[test]
fn forward_elimination_yields_the_determinant() {
    let p = 11;
    let mut sequence = Sequence::new(0xde7e_0001);
    for _ in 0..300 {
        let n = sequence.next_in(0, 4) as usize;
        let a = generated(&mut sequence, n, n, p);
        let log = Log::default();
        let mut grid = Grid::new(n, n, &a, &log);
        grid.below = true;
        let report = recorder(&log);
        let field = UndecidedResidues {
            p,
            undecided: &[],
            report: &report,
        };
        let pivots = match reduce(&field, &mut grid, n, &mut context()).unwrap() {
            Reduction::Complete(pivots) => pivots,
            Reduction::Undecided(reason) => panic!("undecided {reason}"),
        };
        let log = log.take();
        let mut product = 1;
        let mut swaps = 0;
        for (answers, pivot) in searches(&log) {
            if let Some(value) = pivot {
                product = residue_product(p, product, value);
                swaps += usize::from(answers.len() > 1);
            }
        }
        let expected = determinant(&a, n, p);
        if pivots.len() == n {
            let signed = if swaps % 2 == 1 {
                (p - product) % p
            } else {
                product
            };
            assert_eq!(signed, expected, "{a:?}");
        } else {
            assert_eq!(expected, 0, "{a:?}");
        }
        for (k, &pivot) in pivots.iter().enumerate() {
            for below in k + 1..n {
                assert_eq!(grid.entries[below * n + pivot], 0, "{a:?}");
            }
        }
    }
}

/// An undecided answer before a nonzero one does not stop the search: the
/// nonzero entry becomes the pivot, and the entry that answered undecided,
/// swapped into the last row, is eliminated from it.
#[test]
fn undecided_candidates_are_passed_over() {
    let p = 7;
    let log = Log::default();
    let a = [3, 1, 0, 2, 5, 4];
    let mut grid = Grid::new(3, 2, &a, &log);
    let report = recorder(&log);
    let field = UndecidedResidues {
        p,
        undecided: &[3],
        report: &report,
    };
    let reduction = reduce(&field, &mut grid, 2, &mut context()).unwrap();
    assert_eq!(reduction, Reduction::Complete(vec![0, 1]));
    assert_reduced_form(&a, &grid.entries, &[0, 1], 3, 2, p);
    let log = log.take();
    assert_eq!(
        log[..10],
        [
            Event::Begin,
            Event::Candidate,
            Event::Test(3, ZeroTest::Undecided(3)),
            Event::Candidate,
            Event::Test(0, ZeroTest::Zero),
            Event::Candidate,
            Event::Test(5, ZeroTest::Nonzero),
            Event::Swap,
            Event::Swap,
            Event::Pivot {
                row: 0,
                column: 0,
                value: 5
            },
        ]
    );
    let undecided_target = 10
        + log[10..]
            .iter()
            .position(|event| *event == Event::Test(3, ZeroTest::Undecided(3)))
            .expect("the entry that answered undecided is tested as a target");
    assert_eq!(log[undecided_target + 1], Event::Store);
}

/// A column whose candidates answer zero or undecided ends the reduction with
/// the reason of its first undecided answer, after the earlier pivots and
/// before any further hook. In the last case the entry zero answers
/// undecided, so the second row, which elimination made zero, is undecided.
/// The state `Reduction::Undecided` refines `MathState::Undecided`.
#[test]
fn undecided_columns_end_the_reduction() {
    let p = 7;
    for (entries, undecided, reason) in [
        ([1, 2, 0, 4, 0, 3], vec![4, 3], 4),
        ([1, 2, 0, 0, 0, 3], vec![3], 3),
        ([1, 2, 2, 4, 0, 6], vec![6, 0], 0),
    ] {
        let log = Log::default();
        let mut grid = Grid::new(3, 2, &entries, &log);
        let report = recorder(&log);
        let field = UndecidedResidues {
            p,
            undecided: &undecided,
            report: &report,
        };
        let reduction = reduce(&field, &mut grid, 2, &mut context()).unwrap();
        assert_eq!(reduction, Reduction::Undecided(reason), "{entries:?}");
        let log = log.take();
        assert!(!log.contains(&Event::End));
        assert_eq!(
            log.iter()
                .filter(|event| matches!(event, Event::Pivot { .. }))
                .count(),
            1
        );
        assert!(matches!(log.last(), Some(Event::Test(..))), "{log:?}");
        assert_eq!(grid.entries[..2], [1, 2]);
    }
}

/// Over generated matrices with generated sets of values that answer
/// undecided, every pivot answered nonzero after zero and undecided answers
/// only, a reduction is undecided exactly when its last search found no
/// nonzero answer and at least one undecided one, with the first as its
/// reason, and a complete reduction is the reduced row echelon form.
#[test]
fn undecided_answers_never_become_pivots() {
    let p = 5;
    let mut sequence = Sequence::new(0x0dd_ba11);
    let mut undecided_count = 0;
    let mut complete_with_undecided = 0;
    for _ in 0..400 {
        let rows = sequence.next_in(1, 4) as usize;
        let columns = sequence.next_in(1, 4) as usize;
        let a = generated(&mut sequence, rows, columns, p);
        let undecided: Vec<u32> = (0..p).filter(|_| sequence.next_in(0, 3) == 0).collect();
        case(format_args!("{a:?} with undecided {undecided:?}"), || {
            let log = Log::default();
            let mut grid = Grid::new(rows, columns, &a, &log);
            let report = recorder(&log);
            let field = UndecidedResidues {
                p,
                undecided: &undecided,
                report: &report,
            };
            let reduction = reduce(&field, &mut grid, columns, &mut context()).unwrap();
            let log = log.take();
            let searches = searches(&log);
            for (answers, pivot) in &searches {
                let last = answers.len() - 1;
                assert!(answers[..last].iter().all(|a| *a != ZeroTest::Nonzero));
                assert_eq!(answers[last] == ZeroTest::Nonzero, pivot.is_some());
            }
            match reduction {
                Reduction::Complete(pivots) => {
                    assert_eq!(log.last(), Some(&Event::End));
                    assert_reduced_form(&a, &grid.entries, &pivots, rows, columns, p);
                    if log
                        .iter()
                        .any(|event| matches!(event, Event::Test(_, ZeroTest::Undecided(_))))
                    {
                        complete_with_undecided += 1;
                    }
                }
                Reduction::Undecided(reason) => {
                    undecided_count += 1;
                    let (answers, pivot) = searches.last().expect("a search");
                    assert_eq!(*pivot, None);
                    let first = answers.iter().find_map(|answer| match answer {
                        ZeroTest::Undecided(reason) => Some(*reason),
                        _ => None,
                    });
                    assert_eq!(first, Some(reason));
                    assert!(matches!(log.last(), Some(Event::Test(..))));
                }
            }
        });
    }
    assert!(undecided_count > 0 && complete_with_undecided > 0);
}

/// The skeleton charges nothing itself: a reduction whose field and storage
/// charge nothing succeeds under an exhausted budget and a cancelled flag,
/// and charges no work.
#[test]
fn the_skeleton_never_charges() {
    let log = Log::default();
    let a = [0, 2, 1, 3, 4, 1, 1, 0, 6];
    let mut grid = Grid::new(3, 3, &a, &log);
    let report = recorder(&log);
    let field = UndecidedResidues {
        p: 7,
        undecided: &[],
        report: &report,
    };
    let flag = CancelFlag::new();
    flag.cancel();
    let mut context = Context::new(Limits::new().with_max_work(0), flag);
    let reduction = reduce(&field, &mut grid, 3, &mut context).unwrap();
    assert_eq!(reduction, Reduction::Complete(vec![0, 1, 2]));
    assert_eq!(context.work_used(), 0);
}

/// A failing hook ends the reduction with its error: for every store of a
/// reduction, a failure of that store is the last event.
#[test]
fn a_failing_hook_ends_the_reduction() {
    let a = [0, 2, 1, 3, 4, 1, 1, 0, 6];
    let full_log = Log::default();
    let mut full = Grid::new(3, 3, &a, &full_log);
    let full_report = recorder(&full_log);
    let field = UndecidedResidues {
        p: 7,
        undecided: &[],
        report: &full_report,
    };
    reduce(&field, &mut full, 3, &mut context()).unwrap();
    assert!(full.stores > 0);
    for fail_at in 0..full.stores {
        let log = Log::default();
        let mut grid = Grid::new(3, 3, &a, &log);
        grid.fail_at = Some(fail_at);
        let report = recorder(&log);
        let field = UndecidedResidues {
            p: 7,
            undecided: &[],
            report: &report,
        };
        let Err(error) = reduce(&field, &mut grid, 3, &mut context()) else {
            panic!("the store {fail_at} did not fail");
        };
        let expected = store_failure();
        assert_eq!(
            (error.kind(), error.span(), error.message()),
            (expected.kind(), expected.span(), expected.message())
        );
        let log = log.take();
        assert_eq!(log.last(), Some(&Event::Store));
        assert_eq!(
            log.iter().filter(|event| **event == Event::Store).count(),
            fail_at + 1
        );
    }
}

/// A storage that checks, in every hook that takes the context, that the
/// open frames and the retained storage are those of the caller.
struct Watched<'a> {
    inner: Grid<'a>,
    frames: u64,
    retained: Storage,
    checks: std::cell::Cell<usize>,
}

impl Watched<'_> {
    fn check(&self, context: &Context) {
        assert_eq!(context.open_frames(), self.frames);
        assert_eq!(context.retained(), self.retained);
        self.checks.set(self.checks.get() + 1);
    }
}

impl EliminationRows for Watched<'_> {
    type Element = u32;

    fn rows(&self) -> usize {
        self.inner.rows()
    }

    fn width(&self) -> usize {
        self.inner.width()
    }

    fn entry(&self, row: usize, column: usize) -> &u32 {
        self.inner.entry(row, column)
    }

    fn begin_reduction(&mut self, variables: usize, context: &mut Context) -> Result<Vec<usize>> {
        self.check(context);
        self.inner.begin_reduction(variables, context)
    }

    fn candidate_step(&self, context: &mut Context) -> Result<()> {
        self.check(context);
        self.inner.candidate_step(context)
    }

    fn swap_cell(
        &mut self,
        row: usize,
        other: usize,
        column: usize,
        context: &mut Context,
    ) -> Result<()> {
        self.check(context);
        self.inner.swap_cell(row, other, column, context)
    }

    fn begin_pivot(
        &mut self,
        row: usize,
        column: usize,
        swapped: bool,
        context: &mut Context,
    ) -> Result<u32> {
        self.check(context);
        self.inner.begin_pivot(row, column, swapped, context)
    }

    fn store(
        &mut self,
        row: usize,
        column: usize,
        value: u32,
        context: &mut Context,
    ) -> Result<()> {
        self.check(context);
        self.inner.store(row, column, value, context)
    }

    fn first_target(&self, row: usize) -> usize {
        self.inner.first_target(row)
    }

    fn target_step(&self, context: &mut Context) -> Result<()> {
        self.check(context);
        self.inner.target_step(context)
    }

    fn end_pivot(&mut self, row: usize, column: usize, context: &mut Context) -> Result<()> {
        self.check(context);
        self.inner.end_pivot(row, column, context)
    }

    fn reserve_pivot(&mut self, pivots: &mut Vec<usize>, context: &mut Context) -> Result<()> {
        self.check(context);
        self.inner.reserve_pivot(pivots, context)
    }

    fn end_reduction(&mut self, context: &mut Context) -> Result<()> {
        self.check(context);
        self.inner.end_reduction(context)
    }
}

/// The skeleton holds no frame and no reservation: under a caller that has
/// opened a frame and reserved storage, every hook sees exactly that frame
/// and that reservation, and so does the caller after the reduction.
#[test]
fn the_skeleton_holds_no_frame_and_no_reservation() {
    let mut context = context();
    let frame = context.enter_frame().unwrap();
    let reserved = context.reserve(Storage::new(3, 48)).unwrap();
    let frames = context.open_frames();
    let retained = context.retained();
    assert_eq!((frames, retained), (1, Storage::new(3, 48)));
    let log = Log::default();
    let a = [0, 2, 1, 3, 4, 1, 1, 0, 6];
    let mut rows = Watched {
        inner: Grid::new(3, 3, &a, &log),
        frames,
        retained,
        checks: std::cell::Cell::new(0),
    };
    let report = recorder(&log);
    let field = UndecidedResidues {
        p: 7,
        undecided: &[],
        report: &report,
    };
    let reduction = reduce(&field, &mut rows, 3, &mut context).unwrap();
    assert_eq!(reduction, Reduction::Complete(vec![0, 1, 2]));
    assert!(rows.checks.get() > 20, "{}", rows.checks.get());
    assert_eq!(
        (context.open_frames(), context.retained()),
        (frames, retained)
    );
    context.release(reserved);
    context.leave_frame(frame);
}

// ---------------------------------------------------------------------------
// The properties of the qualification case of the earlier implementation,
// restated as unit tests

/// The answer of the pivot search from `row` in the single column of
/// `entries`, over the residues modulo 7 that answer undecided for
/// `undecided`, and the events that it logged.
fn search(
    entries: &[u32],
    rows: usize,
    undecided: &[u32],
    row: usize,
) -> ((ZeroTest<u32>, usize), Vec<Event>) {
    let log = Log::default();
    let grid = Grid::new(rows, 1, entries, &log);
    let report = recorder(&log);
    let field = UndecidedResidues {
        p: 7,
        undecided,
        report: &report,
    };
    let found = find_pivot(&field, &grid, row, 0, &mut context()).unwrap();
    (found, log.take())
}

/// A candidate whose test answers nonzero ends the search: it is the pivot,
/// and no later candidate is tested.
#[test]
fn the_search_stops_at_the_first_nonzero_answer() {
    let (found, log) = search(&[5, 0, 3], 3, &[], 0);
    assert_eq!(found, (ZeroTest::Nonzero, 0));
    assert_eq!(log, [Event::Candidate, Event::Test(5, ZeroTest::Nonzero)]);
    let (found, log) = search(&[0, 4, 2], 3, &[], 0);
    assert_eq!(found, (ZeroTest::Nonzero, 1));
    assert_eq!(log.len(), 4);
}

/// A candidate whose test answers zero is passed over, and the answer of the
/// column stays zero.
#[test]
fn the_search_passes_over_a_zero_answer() {
    let (found, log) = search(&[0, 0], 2, &[], 0);
    assert_eq!(found, (ZeroTest::Zero, 2));
    assert_eq!(
        log,
        [
            Event::Candidate,
            Event::Test(0, ZeroTest::Zero),
            Event::Candidate,
            Event::Test(0, ZeroTest::Zero),
        ]
    );
}

/// A candidate whose test answers undecided is passed over too; the search
/// remembers the first undecided answer, and a later nonzero answer still
/// ends it with its pivot.
#[test]
fn the_search_passes_over_an_undecided_answer_and_remembers_the_first() {
    let (found, log) = search(&[3, 4, 0], 3, &[3, 4], 0);
    assert_eq!(found, (ZeroTest::Undecided(3), 3));
    assert_eq!(log.len(), 6);
    let (found, _) = search(&[3, 2], 2, &[3], 0);
    assert_eq!(found, (ZeroTest::Nonzero, 1));
}

/// After the last candidate the search returns the answer of the column,
/// with the index past the last row.
#[test]
fn after_the_last_candidate_the_search_returns_the_answer_of_the_column() {
    let (found, log) = search(&[2, 0], 2, &[], 2);
    assert_eq!(found, (ZeroTest::Zero, 2));
    assert!(log.is_empty());
    let (found, _) = search(&[2, 0, 3], 3, &[3], 1);
    assert_eq!(found, (ZeroTest::Undecided(3), 3));
}

/// The first undecided answer of a column that had answered zero so far
/// makes the column undecided.
#[test]
fn the_first_undecided_answer_replaces_zero() {
    assert_eq!(
        first_undecided(ZeroTest::Zero, 4_u32),
        ZeroTest::Undecided(4)
    );
}

/// A later undecided answer keeps the reason of the first.
#[test]
fn a_later_undecided_answer_keeps_the_first_reason() {
    assert_eq!(
        first_undecided(ZeroTest::Undecided(4_u32), 6),
        ZeroTest::Undecided(4)
    );
}

/// A column that answered zero has no pivot: the reduction moves on to the
/// next column with the same row.
#[test]
fn a_column_that_answered_zero_is_passed_over() {
    let log = Log::default();
    let mut grid = Grid::new(2, 2, &[0, 1, 0, 2], &log);
    let report = recorder(&log);
    let field = UndecidedResidues {
        p: 7,
        undecided: &[],
        report: &report,
    };
    let reduction = reduce_columns(&field, &mut grid, 2, Vec::new(), &mut context()).unwrap();
    assert_eq!(reduction, Reduction::Complete(vec![1]));
    let log = log.take();
    assert_eq!(
        log[..5],
        [
            Event::Candidate,
            Event::Test(0, ZeroTest::Zero),
            Event::Candidate,
            Event::Test(0, ZeroTest::Zero),
            Event::Candidate,
        ]
    );
    assert!(log.contains(&Event::Pivot {
        row: 0,
        column: 1,
        value: 1
    }));
}

/// A column that answered undecided ends the reduction with the undecided
/// state and its reason, without a further hook of the storage and with the
/// storage as it was.
#[test]
fn an_undecided_column_ends_the_reduction_without_a_hook() {
    let log = Log::default();
    let entries = [3, 1, 0, 2];
    let mut grid = Grid::new(2, 2, &entries, &log);
    let report = recorder(&log);
    let field = UndecidedResidues {
        p: 7,
        undecided: &[3],
        report: &report,
    };
    let reduction = reduce_columns(&field, &mut grid, 2, Vec::new(), &mut context()).unwrap();
    assert_eq!(reduction, Reduction::Undecided(3));
    assert_eq!(
        log.take(),
        [
            Event::Candidate,
            Event::Test(3, ZeroTest::Undecided(3)),
            Event::Candidate,
            Event::Test(0, ZeroTest::Zero),
        ]
    );
    assert_eq!(grid.entries, entries);
}

/// An entry of another row whose test answered undecided is eliminated with
/// itself as the factor.
#[test]
fn an_undecided_entry_of_another_row_is_eliminated() {
    let log = Log::default();
    let mut grid = Grid::new(2, 2, &[1, 2, 3, 4], &log);
    let report = recorder(&log);
    let field = UndecidedResidues {
        p: 7,
        undecided: &[3],
        report: &report,
    };
    eliminate_row(&field, &mut grid, 0, 1, 0, &mut context()).unwrap();
    assert_eq!(grid.entries, [1, 2, 0, 5]);
    assert_eq!(
        log.take(),
        [
            Event::Test(3, ZeroTest::Undecided(3)),
            Event::Store,
            Event::Store
        ]
    );
}

/// The reduction over a field that always decides is unwrapped without a
/// failure path.
#[test]
fn a_reduction_over_a_field_that_always_decides_unwraps() {
    assert_eq!(
        complete(Reduction::<Infallible>::Complete(vec![0, 2])),
        [0, 2]
    );
    let log = Log::default();
    let mut grid = Grid::new(2, 3, &[1, 2, 3, 2, 4, 1], &log);
    let reduction = reduce(&ExactResidues { p: 7 }, &mut grid, 3, &mut context()).unwrap();
    assert_eq!(complete(reduction), [0, 2]);
}

/// A column that answered nonzero runs the pivot step at the selected row,
/// with the swap of that row into place, and the reduction moves on with the
/// next column and the next row.
#[test]
fn a_column_that_answered_nonzero_runs_the_pivot_step() {
    let log = Log::default();
    let mut grid = Grid::new(2, 2, &[0, 1, 2, 3], &log);
    let report = recorder(&log);
    let field = UndecidedResidues {
        p: 7,
        undecided: &[],
        report: &report,
    };
    let reduction = reduce_columns(&field, &mut grid, 2, Vec::new(), &mut context()).unwrap();
    assert_eq!(reduction, Reduction::Complete(vec![0, 1]));
    let log = log.take();
    assert_eq!(
        log[..7],
        [
            Event::Candidate,
            Event::Test(0, ZeroTest::Zero),
            Event::Candidate,
            Event::Test(2, ZeroTest::Nonzero),
            Event::Swap,
            Event::Swap,
            Event::Pivot {
                row: 0,
                column: 0,
                value: 2
            },
        ]
    );
    let reserve = log
        .iter()
        .position(|event| *event == Event::Reserve)
        .expect("the first pivot reserves its column");
    assert_eq!(log[reserve - 1], Event::EndPivot);
    assert_eq!(log[reserve + 1], Event::Candidate);
    assert!(log.contains(&Event::Pivot {
        row: 1,
        column: 1,
        value: 1
    }));
}

/// A pivot found in the current row stays in place: the step takes the pivot
/// without a swap, normalizes and eliminates, and appends its column.
#[test]
fn a_pivot_in_the_current_row_stays_in_place() {
    let log = Log::default();
    let mut grid = Grid::new(2, 2, &[2, 4, 1, 1], &log);
    let report = recorder(&log);
    let field = UndecidedResidues {
        p: 7,
        undecided: &[],
        report: &report,
    };
    let mut pivots = Vec::new();
    pivot_step(&field, &mut grid, 0, 0, 0, &mut pivots, &mut context()).unwrap();
    assert_eq!(pivots, [0]);
    let log = log.take();
    assert_eq!(
        log[0],
        Event::Pivot {
            row: 0,
            column: 0,
            value: 2
        }
    );
    assert!(!log.contains(&Event::Swap));
    assert_eq!(log[log.len() - 2..], [Event::EndPivot, Event::Reserve]);
    assert_eq!(grid.entries, [1, 2, 0, 6]);
}

/// Normalization divides each entry of the pivot row from the pivot column
/// on by the pivot and stores it; the entries before that column stay.
#[test]
fn normalization_divides_the_pivot_row_entry_by_entry() {
    let log = Log::default();
    let mut grid = Grid::new(1, 3, &[5, 3, 6], &log);
    let report = recorder(&log);
    let field = UndecidedResidues {
        p: 7,
        undecided: &[],
        report: &report,
    };
    normalize_row(&field, &mut grid, 0, 1, &3, &mut context()).unwrap();
    assert_eq!(grid.entries, [5, 1, 2]);
    assert_eq!(log.take(), [Event::Store, Event::Store]);
}

/// The elimination passes over the pivot row after its step, without
/// testing or changing it.
#[test]
fn the_elimination_passes_over_the_pivot_row() {
    let log = Log::default();
    let mut grid = Grid::new(2, 2, &[1, 3, 0, 4], &log);
    let report = recorder(&log);
    let field = UndecidedResidues {
        p: 7,
        undecided: &[],
        report: &report,
    };
    eliminate_rows(&field, &mut grid, 0, 0, &mut context()).unwrap();
    assert_eq!(
        log.take(),
        [Event::Target, Event::Target, Event::Test(0, ZeroTest::Zero)]
    );
    assert_eq!(grid.entries, [1, 3, 0, 4]);
}

/// The elimination eliminates the pivot from every other row after its
/// step.
#[test]
fn the_elimination_eliminates_from_every_other_row() {
    let log = Log::default();
    let mut grid = Grid::new(3, 2, &[2, 1, 1, 3, 4, 5], &log);
    let report = recorder(&log);
    let field = UndecidedResidues {
        p: 7,
        undecided: &[],
        report: &report,
    };
    eliminate_rows(&field, &mut grid, 1, 0, &mut context()).unwrap();
    assert_eq!(grid.entries, [0, 2, 1, 3, 0, 0]);
    assert_eq!(
        log.take(),
        [
            Event::Target,
            Event::Test(2, ZeroTest::Nonzero),
            Event::Store,
            Event::Store,
            Event::Target,
            Event::Target,
            Event::Test(4, ZeroTest::Nonzero),
            Event::Store,
            Event::Store,
        ]
    );
}

/// An entry of another row whose test answered zero is left as it is.
#[test]
fn a_zero_entry_of_another_row_is_left_as_it_is() {
    let log = Log::default();
    let mut grid = Grid::new(2, 2, &[1, 2, 0, 4], &log);
    let report = recorder(&log);
    let field = UndecidedResidues {
        p: 7,
        undecided: &[],
        report: &report,
    };
    eliminate_row(&field, &mut grid, 0, 1, 0, &mut context()).unwrap();
    assert_eq!(grid.entries, [1, 2, 0, 4]);
    assert_eq!(log.take(), [Event::Test(0, ZeroTest::Zero)]);
}

/// An entry of another row whose test answered nonzero is eliminated with
/// itself as the factor.
#[test]
fn a_nonzero_entry_of_another_row_is_eliminated() {
    let log = Log::default();
    let mut grid = Grid::new(2, 2, &[1, 2, 3, 4], &log);
    let report = recorder(&log);
    let field = UndecidedResidues {
        p: 7,
        undecided: &[],
        report: &report,
    };
    eliminate_row(&field, &mut grid, 0, 1, 0, &mut context()).unwrap();
    assert_eq!(grid.entries, [1, 2, 0, 5]);
    assert_eq!(
        log.take(),
        [
            Event::Test(3, ZeroTest::Nonzero),
            Event::Store,
            Event::Store
        ]
    );
}

/// Row subtraction replaces each entry of the other row from the column on
/// by its difference with the factor times the entry of the pivot row.
#[test]
fn row_subtraction_replaces_each_entry_by_its_difference() {
    let log = Log::default();
    let mut grid = Grid::new(2, 3, &[1, 3, 5, 6, 4, 2], &log);
    let report = recorder(&log);
    let field = UndecidedResidues {
        p: 7,
        undecided: &[],
        report: &report,
    };
    subtract_row(&field, &mut grid, 0, 1, 1, &2, &mut context()).unwrap();
    assert_eq!(grid.entries, [1, 3, 5, 6, 5, 6]);
    assert_eq!(log.take(), [Event::Store, Event::Store]);
}

/// Over $\mathbb F_5$ with the zero test answering undecided for 3, the
/// reduction of the single entry 3 is undecided with the reason 3.
#[test]
fn a_single_undecided_entry_gives_an_undecided_reduction() {
    let log = Log::default();
    let mut grid = Grid::new(1, 1, &[3], &log);
    let report = recorder(&log);
    let field = UndecidedResidues {
        p: 5,
        undecided: &[3],
        report: &report,
    };
    let reduction = reduce(&field, &mut grid, 1, &mut context()).unwrap();
    assert_eq!(reduction, Reduction::Undecided(3));
    assert_eq!(
        log.take(),
        [
            Event::Begin,
            Event::Candidate,
            Event::Test(3, ZeroTest::Undecided(3))
        ]
    );
}

// ---------------------------------------------------------------------------
// The prime fields of the library

/// The primes of the generated eliminations over prime fields.
const PRIMES: [u32; 7] = [2, 3, 5, 7, 251, 65_521, 4_294_967_291];

/// A storage of prime residues that charges one unit in every hook that
/// takes the context, as a caller's storage does.
struct Charged {
    rows: usize,
    width: usize,
    entries: Vec<PrimeResidue>,
}

impl EliminationRows for Charged {
    type Element = PrimeResidue;

    fn rows(&self) -> usize {
        self.rows
    }

    fn width(&self) -> usize {
        self.width
    }

    fn entry(&self, row: usize, column: usize) -> &PrimeResidue {
        &self.entries[row * self.width + column]
    }

    fn begin_reduction(&mut self, _variables: usize, context: &mut Context) -> Result<Vec<usize>> {
        context.charge(1)?;
        Ok(Vec::new())
    }

    fn candidate_step(&self, context: &mut Context) -> Result<()> {
        context.charge(1)
    }

    fn swap_cell(
        &mut self,
        row: usize,
        other: usize,
        column: usize,
        context: &mut Context,
    ) -> Result<()> {
        context.charge(1)?;
        self.entries
            .swap(row * self.width + column, other * self.width + column);
        Ok(())
    }

    fn begin_pivot(
        &mut self,
        row: usize,
        column: usize,
        _swapped: bool,
        context: &mut Context,
    ) -> Result<PrimeResidue> {
        context.charge(1)?;
        Ok(self.entries[row * self.width + column])
    }

    fn store(
        &mut self,
        row: usize,
        column: usize,
        value: PrimeResidue,
        context: &mut Context,
    ) -> Result<()> {
        context.charge(1)?;
        self.entries[row * self.width + column] = value;
        Ok(())
    }

    fn first_target(&self, _row: usize) -> usize {
        0
    }

    fn target_step(&self, context: &mut Context) -> Result<()> {
        context.charge(1)
    }

    fn end_pivot(&mut self, _row: usize, _column: usize, context: &mut Context) -> Result<()> {
        context.charge(1)
    }

    fn reserve_pivot(&mut self, _pivots: &mut Vec<usize>, context: &mut Context) -> Result<()> {
        context.charge(1)
    }

    fn end_reduction(&mut self, context: &mut Context) -> Result<()> {
        context.charge(1)
    }
}

/// A matrix over a prime field, the input of the representative operation.
#[derive(Clone, Debug, PartialEq)]
struct Input {
    p: u32,
    rows: usize,
    width: usize,
    variables: usize,
    entries: Vec<u32>,
}

impl Input {
    /// The field and the residues of the entries, built under a context of
    /// their own.
    fn residues(&self) -> (PrimeField, Vec<PrimeResidue>) {
        let mut scratch = context();
        let field = PrimeField::new(self.p, &mut scratch).unwrap();
        let entries = self
            .entries
            .iter()
            .map(|&v| {
                field
                    .from_integer(&Integer::from(u64::from(v)), &mut scratch)
                    .unwrap()
            })
            .collect();
        (field, entries)
    }
}

/// The representative operation of the resource tests: the reduction of
/// `entries` over `field` in a storage that charges one unit per hook, with
/// the room of the storage reserved by the caller for the time of the
/// reduction. It returns the pivot columns and the reduced entries.
fn eliminate(
    field: &PrimeField,
    input: &Input,
    entries: &[PrimeResidue],
    context: &mut Context,
) -> Result<(Vec<usize>, Vec<u32>)> {
    let cost = entries
        .iter()
        .fold(Storage::ZERO, |sum, e| sum.saturating_add(field.measure(e)));
    let reserved = context.reserve(cost)?;
    let mut rows = Charged {
        rows: input.rows,
        width: input.width,
        entries: entries.to_vec(),
    };
    let reduction = reduce(field, &mut rows, input.variables, context);
    context.release(reserved);
    let pivots = complete(reduction?);
    Ok((
        pivots,
        rows.entries.iter().map(PrimeResidue::value).collect(),
    ))
}

/// The storage that `eliminate` reserves for `input`.
fn reserved_storage(input: &Input) -> Storage {
    let (field, entries) = input.residues();
    entries
        .iter()
        .fold(Storage::ZERO, |sum, e| sum.saturating_add(field.measure(e)))
}

/// Gauss–Jordan elimination of `input` written out over machine integers:
/// for each of the first `variables` columns while rows remain, the first
/// nonzero entry at or below the current row is the pivot, its row is
/// swapped into place and divided by it from the pivot column on, and the
/// pivot is eliminated from every other row with a nonzero entry.
fn naive(input: &Input) -> (Vec<usize>, Vec<u32>) {
    let p = u64::from(input.p);
    let width = input.width;
    let mut a: Vec<u64> = input.entries.iter().map(|&v| u64::from(v)).collect();
    let power = |mut base: u64, mut exponent: u64| {
        let mut result = 1 % p;
        while exponent > 0 {
            if exponent & 1 == 1 {
                result = result * base % p;
            }
            base = base * base % p;
            exponent >>= 1;
        }
        result
    };
    let mut pivots = Vec::new();
    for column in 0..input.variables {
        let row = pivots.len();
        if row == input.rows {
            break;
        }
        let Some(selected) = (row..input.rows).find(|&r| a[r * width + column] != 0) else {
            continue;
        };
        for c in 0..width {
            a.swap(row * width + c, selected * width + c);
        }
        let inverse = power(a[row * width + column], p - 2);
        for c in column..width {
            a[row * width + c] = a[row * width + c] * inverse % p;
        }
        for other in 0..input.rows {
            let factor = a[other * width + column];
            if other != row && factor != 0 {
                for c in column..width {
                    let product = factor * a[row * width + c] % p;
                    a[other * width + c] = (a[other * width + c] + p - product) % p;
                }
            }
        }
        pivots.push(column);
    }
    (pivots, a.iter().map(|&v| v as u32).collect())
}

/// A generated matrix over one of `PRIMES`, with at most 6 rows, at most 8
/// columns and a generated number of variables.
fn generated_input(sequence: &mut Sequence) -> Input {
    let p = *sequence.pick(&PRIMES);
    let rows = sequence.next_in(0, 6) as usize;
    let width = sequence.next_in(0, 8) as usize;
    let variables = sequence.next_in(0, width as i64) as usize;
    let entries = (0..rows * width)
        .map(|_| match sequence.next_in(0, 3) {
            0 => 0,
            1 => p - 1,
            _ => sequence.next_in(0, i64::from(p) - 1) as u32,
        })
        .collect();
    Input {
        p,
        rows,
        width,
        variables,
        entries,
    }
}

/// Over the prime fields of the library, the skeleton gives the pivot
/// columns and the entries of the naive elimination, for 1,000 generated
/// matrices.
#[test]
fn reductions_over_prime_fields_match_naive_elimination() {
    let mut sequence = Sequence::new(0xe11a_0001);
    for _ in 0..1000 {
        let input = generated_input(&mut sequence);
        case(format_args!("{input:?}"), || {
            let (field, entries) = input.residues();
            let found = eliminate(&field, &input, &entries, &mut context()).unwrap();
            assert_eq!(found, naive(&input));
        });
    }
}

// ---------------------------------------------------------------------------
// Resource limits, cancellation and rollback

/// The representative inputs B01 to B03.
fn representative() -> [Input; 3] {
    let p = 4_294_967_291;
    [
        Input {
            p: 7,
            rows: 3,
            width: 3,
            variables: 3,
            entries: vec![0, 2, 1, 3, 1, 4, 5, 6, 2],
        },
        Input {
            p: 5,
            rows: 3,
            width: 4,
            variables: 4,
            entries: vec![0, 1, 2, 3, 0, 2, 4, 1, 0, 3, 1, 0],
        },
        Input {
            p,
            rows: 2,
            width: 3,
            variables: 2,
            entries: vec![p - 1, 2, 5, 3, p - 2, 7],
        },
    ]
}

/// The expected pivot columns of B01 to B03.
const REPRESENTATIVE_PIVOTS: [&[usize]; 3] = [&[0, 1, 2], &[1, 3], &[0, 1]];

/// The work that `eliminate` charges for `input` under the default limits.
fn measured_work(input: &Input) -> u64 {
    let (field, entries) = input.residues();
    let mut context = context();
    eliminate(&field, input, &entries, &mut context).unwrap();
    context.work_used()
}

/// Runs `eliminate` for `input` under `context`, checks that the input and
/// the retained storage are unchanged afterwards, and returns the result.
fn run(input: &Input, context: &mut Context) -> Result<(Vec<usize>, Vec<u32>)> {
    let copy = input.clone();
    let (field, entries) = input.residues();
    let before = context.retained();
    let result = eliminate(&field, input, &entries, context);
    assert_eq!(context.retained(), before);
    assert_eq!(*input, copy);
    let values: Vec<u32> = entries.iter().map(PrimeResidue::value).collect();
    assert_eq!(values, input.entries);
    result
}

/// Asserts that `result` failed with `ResourceLimit` on `field`.
fn assert_limit(result: Result<(Vec<usize>, Vec<u32>)>, field: LimitField) {
    let Err(error) = result else {
        panic!("the elimination succeeded");
    };
    assert_eq!(error.kind(), ErrorKind::ResourceLimit);
    assert_eq!(
        error.exceeded().map(|exceeded| exceeded.id().clone()),
        Some(LimitId::Field(field))
    );
}

/// With exactly the work it charges an elimination succeeds, and with one
/// unit less it fails with `ResourceLimit` on `max_work`.
#[test]
fn an_elimination_over_a_prime_field_passes_at_the_exact_work_and_fails_one_unit_below() {
    for (input, pivots) in representative().iter().zip(REPRESENTATIVE_PIVOTS) {
        let work = measured_work(input);
        let mut exact = Context::new(Limits::new().with_max_work(work), CancelFlag::new());
        let (found, entries) = run(input, &mut exact).unwrap();
        assert_eq!((found.as_slice(), entries), (pivots, naive(input).1));
        let mut below = Context::new(Limits::new().with_max_work(work - 1), CancelFlag::new());
        assert_limit(run(input, &mut below), LimitField::Work);
    }
}

/// With exactly the storage of its rows an elimination succeeds, and with
/// one byte less the reservation of its caller fails with `ResourceLimit` on
/// `max_storage_bytes`.
#[test]
fn an_elimination_over_a_prime_field_passes_at_the_exact_storage_and_fails_one_byte_below() {
    for (input, pivots) in representative().iter().zip(REPRESENTATIVE_PIVOTS) {
        let bytes = reserved_storage(input).bytes;
        let mut exact = Context::new(
            Limits::new().with_max_storage_bytes(bytes),
            CancelFlag::new(),
        );
        let (found, _) = run(input, &mut exact).unwrap();
        assert_eq!(found, pivots);
        let mut below = Context::new(
            Limits::new().with_max_storage_bytes(bytes - 1),
            CancelFlag::new(),
        );
        assert_limit(run(input, &mut below), LimitField::StorageBytes);
    }
}

/// A probe that counts its polls and reports cancellation from the poll
/// after the first `cancel_after` polls on.
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

/// A clock that stays at 0.
#[derive(Clone, Copy)]
struct StoppedClock;

impl Clock for StoppedClock {
    fn now(&mut self) -> u64 {
        0
    }

    fn fork(&self) -> Box<dyn Clock> {
        Box::new(*self)
    }
}

/// A context under the default limits on a stopped clock, polling `probe`.
fn observed(probe: &CountingProbe) -> Context {
    Context::with_observers(
        Limits::new(),
        Box::new(StoppedClock),
        Box::new(probe.clone()),
    )
    .with_deadline(u64::MAX)
}

/// The number of charges of `eliminate` for `input` that poll the probe.
fn charge_points(input: &Input) -> u64 {
    let probe = CountingProbe::after(u64::MAX);
    run(input, &mut observed(&probe)).unwrap();
    probe.polls()
}

/// A cancellation observed at any one of the charges of an elimination ends
/// it with `Cancelled`.
#[test]
fn cancellation_at_every_charge_of_an_elimination_is_reported() {
    for input in &representative() {
        let points = charge_points(input);
        assert!(points > 0);
        for k in 0..points {
            let probe = CountingProbe::after(k);
            let Err(error) = run(input, &mut observed(&probe)) else {
                panic!("not cancelled at charge {}", k + 1);
            };
            assert_eq!(error.kind(), ErrorKind::Cancelled, "charge {}", k + 1);
        }
    }
}

/// After every failure and cancellation of the representative eliminations,
/// the input of the caller is unchanged and the retained storage is that
/// before the call; `run` checks both, and no output is written.
#[test]
fn a_failed_or_cancelled_elimination_keeps_its_input_and_the_retained_storage() {
    for input in &representative() {
        let work = measured_work(input);
        let bytes = reserved_storage(input).bytes;
        let mut failures = 0;
        for limits in [
            Limits::new().with_max_work(work - 1),
            Limits::new().with_max_work(work / 2),
            Limits::new().with_max_work(0),
            Limits::new().with_max_storage_bytes(bytes - 1),
        ] {
            let mut context = Context::new(limits, CancelFlag::new());
            let reserved = context.reserve(Storage::new(1, 8)).unwrap();
            assert!(run(input, &mut context).is_err());
            assert_eq!(context.retained(), Storage::new(1, 8));
            assert_eq!(context.output_used(), 0);
            context.release(reserved);
            failures += 1;
        }
        for k in 0..charge_points(input) {
            let probe = CountingProbe::after(k);
            let mut context = observed(&probe);
            assert!(run(input, &mut context).is_err());
            assert_eq!(context.retained(), Storage::ZERO);
            failures += 1;
        }
        assert!(failures > 4);
    }
}

/// Generated eliminations under generated limits and cancellation points do
/// not panic: each ends with its result, `ResourceLimit` or `Cancelled`, and
/// leaves the retained storage as it was.
#[test]
fn random_eliminations_over_prime_fields_do_not_panic() {
    let mut sequence = Sequence::new(0xe11a_0002);
    for _ in 0..1000 {
        let input = generated_input(&mut sequence);
        let work = sequence.next_in(0, 400) as u64;
        let bytes = sequence.next_in(0, 400) as u64;
        let cancel_after = sequence.next_in(0, 400) as u64;
        case(
            format_args!("{input:?} under work {work}, bytes {bytes}, cancel after {cancel_after}"),
            || {
                let probe = CountingProbe::after(cancel_after);
                let limits = Limits::new()
                    .with_max_work(work)
                    .with_max_storage_bytes(bytes);
                let mut context =
                    Context::with_observers(limits, Box::new(StoppedClock), Box::new(probe))
                        .with_deadline(u64::MAX);
                match run(&input, &mut context) {
                    Ok(found) => assert_eq!(found, naive(&input)),
                    Err(error) => assert!(
                        matches!(
                            error.kind(),
                            ErrorKind::ResourceLimit | ErrorKind::Cancelled
                        ),
                        "{error:?}"
                    ),
                }
            },
        );
    }
}
