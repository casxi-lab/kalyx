//! The public interface of the request context, as code outside the library
//! sees it: the contract tests of its requirements, the absence of hidden
//! caps, determinism, the deadline and cancellation, bounded output, and the
//! accounting of frames and temporaries. Tests whose outcome depends on when
//! a deadline passes use a fake clock, except the host tests; the tests of the
//! default flag and the carried-over examples with a deadline at the current
//! reading or an hour away use `Context::new`, so no test depends on the speed
//! of a clock. Errors are compared by kind and exceeded limit, never by
//! message.

#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    reason = "the helpers of the tests unwrap their results, as the tests do"
)]

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};

use kalyx::context::{
    CancelFlag, CancelProbe, Clock, LARGE_CHARGE, POLL_WINDOW, Storage, StorageCost, overrun_bound,
};
use kalyx::{
    Context, Error, ErrorKind, LimitAmount, LimitExceeded, LimitField, LimitId, LimitScope, Limits,
    Result,
};

// ---------------------------------------------------------------------------
// Fakes and helpers

/// A clock whose reading the test sets, counting its readings.
#[derive(Clone, Default)]
struct FakeClock {
    now: Arc<AtomicU64>,
    reads: Arc<AtomicU64>,
}

impl FakeClock {
    fn at(now: u64) -> Self {
        let clock = Self::default();
        clock.set(now);
        clock
    }

    fn set(&self, now: u64) {
        self.now.store(now, Ordering::SeqCst);
    }

    fn reads(&self) -> u64 {
        self.reads.load(Ordering::SeqCst)
    }
}

impl Clock for FakeClock {
    fn now(&mut self) -> u64 {
        self.reads.fetch_add(1, Ordering::SeqCst);
        self.now.load(Ordering::SeqCst)
    }

    fn fork(&self) -> Box<dyn Clock> {
        Box::new(self.clone())
    }
}

/// A probe that counts its polls and is cancelled by the test.
#[derive(Clone, Default)]
struct FakeProbe {
    cancelled: Arc<AtomicBool>,
    polls: Arc<AtomicU64>,
}

impl FakeProbe {
    fn cancel(&self) {
        self.cancelled.store(true, Ordering::SeqCst);
    }

    fn polls(&self) -> u64 {
        self.polls.load(Ordering::SeqCst)
    }
}

impl CancelProbe for FakeProbe {
    fn is_cancelled(&mut self) -> bool {
        self.polls.fetch_add(1, Ordering::SeqCst);
        self.cancelled.load(Ordering::SeqCst)
    }

    fn fork(&self) -> Box<dyn CancelProbe> {
        Box::new(self.clone())
    }
}

fn context(limits: Limits, clock: &FakeClock, probe: &FakeProbe) -> Context {
    Context::with_observers(limits, Box::new(clock.clone()), Box::new(probe.clone()))
}

fn plain(limits: Limits) -> Context {
    context(limits, &FakeClock::at(0), &FakeProbe::default())
}

fn budget(max_work: u64) -> Context {
    Context::new(Limits::new().with_max_work(max_work), CancelFlag::new())
}

fn kind<T>(result: Result<T>) -> Option<ErrorKind> {
    match result {
        Ok(_) => None,
        Err(error) => Some(error.kind()),
    }
}

fn exceeded<T>(result: Result<T>) -> Option<LimitExceeded> {
    match result {
        Ok(_) => None,
        Err(error) => error.exceeded().cloned(),
    }
}

/// The identifier, scope, allowed value and amount of an exceeded limit.
fn limit<T>(result: Result<T>) -> (LimitId, Option<LimitScope>, u64, LimitAmount) {
    let exceeded = exceeded(result).expect("a resource limit");
    (
        exceeded.id().clone(),
        exceeded.scope(),
        exceeded.allowed(),
        exceeded.amount(),
    )
}

fn field(field: LimitField) -> LimitId {
    LimitId::Field(field)
}

// ---------------------------------------------------------------------------
// A toy request: the coefficients of $(x + 1)^n$ by Pascal's rule. It checks
// the exponent against `max_exponent`, reserves its row as a temporary, opens
// one frame per row whose cost is the row being built, and charges one unit
// per coefficient. Its charges depend only on $n$.

struct Row<'a>(&'a [u64]);

impl StorageCost for Row<'_> {
    /// One node per coefficient, and the bit length of each as its bytes.
    fn storage(&self) -> Storage {
        let mut cost = Storage::ZERO;
        for value in self.0 {
            cost = cost.saturating_add(Storage::new(
                1,
                u64::from(u64::BITS - value.leading_zeros()),
            ));
        }
        cost
    }
}

fn binomial_row(n: u64, context: &mut Context) -> Result<Vec<u64>> {
    context.check(LimitField::Exponent, n)?;
    let reserved = context.reserve(Storage::new(n + 1, 0))?;
    let mut row = vec![1_u64];
    for _ in 0..n {
        let frame = context.enter_frame()?;
        let mut next = vec![1_u64];
        for i in 1..row.len() {
            context.charge(1)?;
            next.push(row[i - 1] + row[i]);
        }
        next.push(1);
        context.set_frame_cost(&frame, Row(&next).storage())?;
        row = next;
        context.leave_frame(frame);
    }
    context.check_storage(Row(&row).storage(), LimitScope::Value)?;
    context.release(reserved);
    Ok(row)
}

/// The work of `binomial_row(n, ..)`: $n$ frames, $n$ frame costs and
/// $0 + 1 + \dots + (n - 1)$ coefficients.
fn row_work(n: u64) -> u64 {
    2 * n + n * n.saturating_sub(1) / 2
}

type Run = (Option<Vec<u64>>, Option<ErrorKind>, u64, u64, u64, Storage);

fn run(limits: Limits, n: u64) -> Run {
    let clock = FakeClock::at(0);
    let probe = FakeProbe::default();
    let mut c = context(limits, &clock, &probe).with_deadline(u64::MAX);
    let result = binomial_row(n, &mut c);
    let error = result.as_ref().err().map(Error::kind);
    (
        result.ok(),
        error,
        c.work_used(),
        clock.reads(),
        probe.polls(),
        c.retained(),
    )
}

// ---------------------------------------------------------------------------
// Limits: nine fields, each with a default

#[test]
fn limits_have_nine_fields_each_with_a_default() {
    assert_eq!(LimitField::ALL.len(), 9);
    let defaults = Limits::default();
    assert_eq!(defaults, Limits::new());
    let expected = [
        100_000, 65_536, 65_536, 128, 8_192, 262_144, 4_096, 4_096, 32,
    ];
    for (&field, value) in LimitField::ALL.iter().zip(expected) {
        assert_eq!(defaults.get(field), value, "{field:?}");
    }
    assert!(defaults.max_output_bytes <= defaults.max_work);
}

#[test]
fn each_builder_sets_exactly_its_field() {
    let builders: [fn(Limits, u64) -> Limits; 9] = [
        Limits::with_max_work,
        Limits::with_max_input_bytes,
        Limits::with_max_output_bytes,
        Limits::with_max_depth,
        Limits::with_max_nodes,
        Limits::with_max_storage_bytes,
        Limits::with_max_integer_bits,
        Limits::with_max_exponent,
        Limits::with_max_frames,
    ];
    for (index, builder) in builders.iter().enumerate() {
        let limits = builder(Limits::new(), 7);
        for (other, &field) in LimitField::ALL.iter().enumerate() {
            let expected = if other == index {
                7
            } else {
                Limits::new().get(field)
            };
            assert_eq!(limits.get(field), expected, "{field:?}");
        }
    }
}

// ---------------------------------------------------------------------------
// No hidden caps: each field is applied as given, beyond the caps of the
// earlier implementation (8 and 64 frames, depths of 128 and 256, a degree of
// 256, 65536 retained nodes and 1048576 retained bytes).

/// A field checked through `check` admits `value` and rejects `value + 1`,
/// naming the field.
fn admits_exactly(context: &Context, checked: LimitField, value: u64) {
    assert!(context.check(checked, value).is_ok(), "{checked:?} {value}");
    let (id, _, allowed, amount) = limit(context.check(checked, value + 1));
    assert_eq!(id, field(checked));
    assert_eq!(allowed, value);
    assert_eq!(amount, LimitAmount::Required(value + 1));
}

#[test]
fn no_hidden_cap_on_max_work() {
    let big = 1_u64 << 40;
    let mut c = plain(Limits::new().with_max_work(big));
    c.charge(big).unwrap();
    assert_eq!(c.work_used(), big);
    assert_eq!(
        limit(c.charge(1)),
        (
            field(LimitField::Work),
            None,
            big,
            LimitAmount::Required(big + 1)
        )
    );
}

#[test]
fn no_hidden_cap_on_max_input_bytes() {
    let big = 1_u64 << 40;
    admits_exactly(
        &plain(Limits::new().with_max_input_bytes(big)),
        LimitField::InputBytes,
        big,
    );
}

#[test]
fn no_hidden_cap_on_max_output_bytes() {
    let big = 1_u64 << 40;
    let mut c = plain(
        Limits::new()
            .with_max_output_bytes(big)
            .with_max_work(u64::MAX),
    );
    c.charge_output(big).unwrap();
    assert_eq!((c.output_used(), c.work_used()), (big, big));
    assert_eq!(
        limit(c.charge_output(1)),
        (
            field(LimitField::OutputBytes),
            None,
            big,
            LimitAmount::Required(big + 1)
        )
    );
}

#[test]
fn no_hidden_cap_on_max_depth() {
    for value in [9, 65, 129, 257] {
        admits_exactly(
            &plain(Limits::new().with_max_depth(value)),
            LimitField::Depth,
            value,
        );
    }
}

#[test]
fn no_hidden_cap_on_max_nodes() {
    let big = 1_u64 << 40;
    let mut c = plain(Limits::new().with_max_nodes(big).with_max_frames(300));
    admits_exactly(&c, LimitField::Nodes, big);
    let mut frames = Vec::new();
    for _ in 0..257 {
        let frame = c.enter_frame().unwrap();
        c.set_frame_cost(&frame, Storage::new(1 << 30, 0)).unwrap();
        frames.push(frame);
    }
    let rest = c.reserve(Storage::new(big - (257 << 30), 0)).unwrap();
    assert_eq!(c.retained().nodes, big);
    assert!(c.reserve(Storage::new(1, 0)).is_err());
    c.release(rest);
    while let Some(frame) = frames.pop() {
        c.leave_frame(frame);
    }
    assert_eq!(c.retained(), Storage::ZERO);
}

#[test]
fn no_hidden_cap_on_max_storage_bytes() {
    let big = 1_u64 << 40;
    let mut c = plain(Limits::new().with_max_storage_bytes(big));
    admits_exactly(&c, LimitField::StorageBytes, big);
    let frame = c.enter_frame().unwrap();
    c.set_frame_cost(&frame, Storage::new(0, big / 2)).unwrap();
    let rest = c.reserve(Storage::new(0, big / 2)).unwrap();
    assert_eq!(c.retained().bytes, big);
    assert!(
        c.check_storage(Storage::new(0, 1), LimitScope::Value)
            .is_err()
    );
    c.release(rest);
    c.leave_frame(frame);
}

#[test]
fn no_hidden_cap_on_max_integer_bits() {
    let big = 1_u64 << 40;
    admits_exactly(
        &plain(Limits::new().with_max_integer_bits(big)),
        LimitField::IntegerBits,
        big,
    );
}

#[test]
fn no_hidden_cap_on_max_exponent() {
    for value in [257, 1_u64 << 40] {
        admits_exactly(
            &plain(Limits::new().with_max_exponent(value)),
            LimitField::Exponent,
            value,
        );
    }
}

#[test]
fn no_hidden_cap_on_max_frames() {
    for value in [9, 65, 129, 257] {
        let mut c = plain(Limits::new().with_max_frames(value));
        let mut frames = Vec::new();
        for _ in 0..value {
            frames.push(c.enter_frame().unwrap());
        }
        assert_eq!(c.open_frames(), value);
        assert_eq!(
            limit(c.enter_frame()),
            (
                field(LimitField::Frames),
                None,
                value,
                LimitAmount::Required(value + 1)
            )
        );
        assert_eq!(c.work_used(), value);
        while let Some(frame) = frames.pop() {
            c.leave_frame(frame);
        }
        assert_eq!(c.open_frames(), 0);
    }
}

// ---------------------------------------------------------------------------
// Determinism

#[test]
fn the_same_request_twice_charges_the_same_work_and_gives_the_same_result() {
    let limits = Limits::new().with_max_frames(100);
    let first = run(limits, 60);
    let second = run(limits, 60);
    assert_eq!(first, second);
    let (row, error, work, _, _, retained) = first;
    assert_eq!(error, None);
    assert_eq!(row.unwrap()[30], 118_264_581_564_861_424);
    assert_eq!(work, row_work(60));
    assert_eq!(retained, Storage::ZERO);
}

/// Charges depend only on the operations: every budget of at least the work
/// gives the same result and work, and one unit less is a resource limit.
#[test]
fn charges_do_not_depend_on_the_budget() {
    let base = Limits::new().with_max_frames(100);
    let (row, _, work, _, _, _) = run(base, 40);
    for extra in [0, 1, 1_000, 1 << 40] {
        let (again, error, again_work, _, _, _) = run(base.with_max_work(work + extra), 40);
        assert_eq!((again, error, again_work), (row.clone(), None, work));
    }
    let (short, error, _, _, _, _) = run(base.with_max_work(work - 1), 40);
    assert_eq!((short, error), (None, Some(ErrorKind::ResourceLimit)));
}

// ---------------------------------------------------------------------------
// Contract tests: one positive and one negative test per requirement

// CTX-R01, positive.
#[test]
fn ctx_r01_charges_add_exactly_within_max_work() {
    let mut c = plain(Limits::new().with_max_work(10));
    c.charge(4).unwrap();
    assert_eq!(c.work_used(), 4);
    c.charge(6).unwrap();
    assert_eq!(c.work_used(), 10);
    c.charge(0).unwrap();
    assert_eq!(c.work_used(), 10);
}

// CTX-R01, negative.
#[test]
fn ctx_r01_a_failed_charge_changes_no_work() {
    let mut c = plain(Limits::new().with_max_work(10));
    c.charge(8).unwrap();
    assert_eq!(
        limit(c.charge(3)),
        (field(LimitField::Work), None, 10, LimitAmount::Required(11))
    );
    assert_eq!(
        limit(c.charge(u64::MAX)),
        (
            field(LimitField::Work),
            None,
            10,
            LimitAmount::Bound(u64::MAX)
        )
    );
    assert_eq!(c.work_used(), 8);
}

// CTX-R02, positive: cancellation, then the deadline, then the work.
#[test]
fn ctx_r02_failures_are_reported_cancellation_then_deadline_then_work() {
    let clock = FakeClock::at(200);
    let probe = FakeProbe::default();
    let mut c = context(Limits::new().with_max_work(0), &clock, &probe).with_deadline(100);
    probe.cancel();
    assert_eq!(kind(c.charge(1)), Some(ErrorKind::Cancelled));
    let mut c = context(
        Limits::new().with_max_work(0),
        &clock,
        &FakeProbe::default(),
    )
    .with_deadline(100);
    assert_eq!(kind(c.charge(1)), Some(ErrorKind::DeadlineExceeded));
    let mut c = context(
        Limits::new().with_max_work(0),
        &FakeClock::at(0),
        &FakeProbe::default(),
    )
    .with_deadline(100);
    assert_eq!(kind(c.charge(1)), Some(ErrorKind::ResourceLimit));
}

// CTX-R02, negative: without a deadline, or with one that the second
// reading finds not reached, exhausted work is only a resource limit.
#[test]
fn ctx_r02_without_an_expiry_exhausted_work_is_a_resource_limit() {
    let mut c = plain(Limits::new().with_max_work(5));
    c.charge(5).unwrap();
    assert_eq!(kind(c.charge(1)), Some(ErrorKind::ResourceLimit));
    let clock = FakeClock::at(0);
    let mut c = context(
        Limits::new().with_max_work(5),
        &clock,
        &FakeProbe::default(),
    )
    .with_deadline(100);
    c.charge(1).unwrap();
    assert_eq!(kind(c.charge(5)), Some(ErrorKind::ResourceLimit));
    assert_eq!(clock.reads(), 2);
}

// CTX-R02: `enter_frame` and `set_frame_cost` check the work limit before
// their own limit, and `charge_output` checks `max_output_bytes` before the
// work limit. Only a failed work check reads the clock once more, so an
// expiry that the polling step did not observe takes precedence over
// exhausted work but not over an exceeded limit of the entry's own.
#[test]
fn each_entry_checks_its_limits_in_a_fixed_order() {
    let limits = Limits::new().with_max_work(0).with_max_frames(0);
    let clock = FakeClock::at(0);
    let mut c = context(limits, &clock, &FakeProbe::default()).with_deadline(100);
    c.charge(0).unwrap();
    clock.set(100);
    assert_eq!(kind(c.enter_frame()), Some(ErrorKind::DeadlineExceeded));
    assert_eq!(clock.reads(), 2);

    let mut both = plain(limits);
    assert_eq!(limit(both.enter_frame()).0, field(LimitField::Work));

    let mut c = plain(Limits::new().with_max_work(1).with_max_nodes(0));
    let frame = c.enter_frame().unwrap();
    assert_eq!(
        limit(c.set_frame_cost(&frame, Storage::new(1, 0))).0,
        field(LimitField::Work)
    );
    c.leave_frame(frame);

    let limits = Limits::new().with_max_work(0).with_max_output_bytes(0);
    let clock = FakeClock::at(0);
    let mut c = context(limits, &clock, &FakeProbe::default()).with_deadline(100);
    c.charge(0).unwrap();
    clock.set(100);
    assert_eq!(limit(c.charge_output(1)).0, field(LimitField::OutputBytes));
    assert_eq!(clock.reads(), 1);
    let mut both = plain(limits);
    assert_eq!(
        limit(both.charge_output(1)).0,
        field(LimitField::OutputBytes)
    );
}

// CTX-R03, positive: the charge after a large charge reads the clock, so a
// deadline that passes right after the reading of a large charge stops the
// next charge.
#[test]
fn ctx_r03_the_charge_after_a_large_charge_reads_the_clock() {
    let clock = FakeClock::at(0);
    let mut c = context(Limits::new(), &clock, &FakeProbe::default()).with_deadline(100);
    c.charge(1).unwrap();
    c.charge(LARGE_CHARGE).unwrap();
    assert_eq!(clock.reads(), 2);
    clock.set(100);
    assert_eq!(kind(c.charge(1)), Some(ErrorKind::DeadlineExceeded));
    assert_eq!(clock.reads(), 3);
}

// CTX-R03, negative: after a small reading, 63 small charges read no clock,
// and a charge that observes cancellation neither reads nor counts.
#[test]
fn ctx_r03_at_most_63_small_charges_pass_without_a_reading() {
    let clock = FakeClock::at(0);
    let probe = FakeProbe::default();
    let mut c = context(Limits::new(), &clock, &probe).with_deadline(100);
    c.charge(1).unwrap();
    for _ in 0..POLL_WINDOW - 1 {
        c.charge(1).unwrap();
    }
    assert_eq!(clock.reads(), 1);
    c.charge(1).unwrap();
    assert_eq!(clock.reads(), 2);

    let cancelled = FakeProbe::default();
    let clock = FakeClock::at(0);
    let mut c = context(Limits::new(), &clock, &cancelled).with_deadline(100);
    c.charge(1).unwrap();
    cancelled.cancel();
    assert_eq!(kind(c.charge(1)), Some(ErrorKind::Cancelled));
    assert_eq!(clock.reads(), 1);
}

// CTX-R04, positive: a cancellation is observed at the next charge point,
// at every kind of charge point, and changes nothing.
#[test]
fn ctx_r04_cancellation_is_observed_at_the_next_charge_point() {
    let clock = FakeClock::at(0);
    let probe = FakeProbe::default();
    let mut c = context(Limits::new(), &clock, &probe).with_deadline(1_000);
    let frame = c.enter_frame().unwrap();
    for _ in 0..4 {
        c.charge(1).unwrap();
    }
    assert_eq!(probe.polls(), 5);
    let (reads, work) = (clock.reads(), c.work_used());
    probe.cancel();
    // A reservation is not a charge point: it polls nothing.
    let reserved = c.reserve(Storage::new(1, 1)).unwrap();
    assert_eq!(probe.polls(), 5);
    assert_eq!(kind(c.charge(1)), Some(ErrorKind::Cancelled));
    assert_eq!(probe.polls(), 6);
    assert_eq!(kind(c.charge(0)), Some(ErrorKind::Cancelled));
    assert_eq!(kind(c.enter_frame()), Some(ErrorKind::Cancelled));
    assert_eq!(
        kind(c.set_frame_cost(&frame, Storage::new(1, 1))),
        Some(ErrorKind::Cancelled)
    );
    assert_eq!(kind(c.charge_output(10)), Some(ErrorKind::Cancelled));
    assert_eq!(
        (c.work_used(), c.output_used(), c.open_frames()),
        (work, 0, 1)
    );
    assert_eq!(c.frame_cost(&frame), Some(Storage::ZERO));
    assert_eq!(clock.reads(), reads);
    c.release(reserved);
    c.leave_frame(frame);
}

// CTX-R04, negative: cancelling one flag does not stop a request whose
// context holds another.
#[test]
fn ctx_r04_cancelling_one_flag_does_not_stop_another_request() {
    let cancelled = CancelFlag::new();
    let mut stopped = Context::new(Limits::new(), cancelled.clone());
    let mut running = Context::new(Limits::new(), CancelFlag::new());
    cancelled.cancel();
    assert_eq!(kind(stopped.charge(1)), Some(ErrorKind::Cancelled));
    running.charge(1).unwrap();
    assert_eq!(running.work_used(), 1);
}

// CTX-R07, positive.
#[test]
fn ctx_r07_an_integer_of_max_integer_bits_is_admitted() {
    let c = plain(Limits::new());
    c.check(LimitField::IntegerBits, 4096).unwrap();
    let c = plain(Limits::new().with_max_integer_bits(10));
    c.check(LimitField::IntegerBits, 10).unwrap();
}

// CTX-R07, negative.
#[test]
fn ctx_r07_one_bit_more_is_a_resource_limit() {
    let c = plain(Limits::new());
    assert_eq!(
        limit(c.check(LimitField::IntegerBits, 4097)),
        (
            field(LimitField::IntegerBits),
            None,
            4096,
            LimitAmount::Required(4097)
        )
    );
}

// CTX-R08, positive: every entry returns on extreme inputs.
#[test]
fn ctx_r08_extreme_inputs_return_without_panicking() {
    let max = Limits::new()
        .with_max_work(u64::MAX)
        .with_max_input_bytes(u64::MAX)
        .with_max_output_bytes(u64::MAX)
        .with_max_depth(u64::MAX)
        .with_max_nodes(u64::MAX)
        .with_max_storage_bytes(u64::MAX)
        .with_max_integer_bits(u64::MAX)
        .with_max_exponent(u64::MAX)
        .with_max_frames(u64::MAX);
    let clock = FakeClock::at(u64::MAX - 1);
    let mut c = context(max, &clock, &FakeProbe::default()).with_deadline(u64::MAX);
    c.charge(u64::MAX).unwrap();
    assert!(c.charge(u64::MAX).is_err());
    assert!(c.charge_output(u64::MAX).is_err());
    for &checked in LimitField::ALL {
        c.check(checked, u64::MAX).unwrap();
    }
    c.check_storage(Storage::new(u64::MAX, u64::MAX), LimitScope::Value)
        .unwrap();
    c.check_parameter("rows", u64::MAX, u64::MAX).unwrap();
    let mut zero = plain(Limits::new().with_max_work(0).with_max_frames(0));
    assert!(zero.enter_frame().is_err());
    assert!(zero.charge_output(0).is_ok());
    let none = zero.reserve(Storage::ZERO).unwrap();
    zero.release(none);
    let far = context(
        Limits::new(),
        &FakeClock::at(u64::MAX),
        &FakeProbe::default(),
    )
    .with_timeout(u64::MAX);
    assert_eq!(far.work_used(), 0);
}

// CTX-R08, negative: sums that do not fit in a `u64` and tokens of closed
// frames are reported or ignored, never a panic.
#[test]
fn ctx_r08_overflowing_sums_and_stale_tokens_are_reported_not_panics() {
    let mut c = plain(
        Limits::new()
            .with_max_nodes(u64::MAX)
            .with_max_storage_bytes(u64::MAX),
    );
    let first = c.reserve(Storage::new(u64::MAX - 1, 0)).unwrap();
    assert_eq!(
        limit(c.reserve(Storage::new(10, 0))),
        (
            field(LimitField::Nodes),
            Some(LimitScope::Temporary),
            u64::MAX,
            LimitAmount::Bound(u64::MAX)
        )
    );
    let frame = c.enter_frame().unwrap();
    assert_eq!(
        limit(c.set_frame_cost(&frame, Storage::new(2, 0))).1,
        Some(LimitScope::Frame)
    );
    c.set_frame_cost(&frame, Storage::new(1, u64::MAX)).unwrap();
    assert_eq!(
        limit(c.reserve(Storage::new(0, 1))).0,
        field(LimitField::StorageBytes)
    );
    assert_eq!(c.retained(), Storage::new(u64::MAX, u64::MAX));
    c.release(first);
    assert_eq!(c.retained(), Storage::new(1, u64::MAX));
    let inner = c.enter_frame().unwrap();
    c.leave_frame(frame);
    assert_eq!(c.retained(), Storage::ZERO);
    c.set_frame_cost(&inner, Storage::new(u64::MAX, u64::MAX))
        .unwrap();
    assert_eq!(c.frame_cost(&inner), None);
    c.leave_frame(inner);
    assert_eq!((c.open_frames(), c.retained()), (0, Storage::ZERO));
    let mut output = plain(Limits::new().with_max_output_bytes(u64::MAX));
    output.charge_output(1).unwrap();
    assert_eq!(
        limit(output.charge_output(u64::MAX)),
        (
            field(LimitField::OutputBytes),
            None,
            u64::MAX,
            LimitAmount::Bound(u64::MAX)
        )
    );
}

// ---------------------------------------------------------------------------
// The scope of an exceeded limit: `Some` exactly for the two retained totals,
// at every entry that reports a limit.

#[test]
fn only_the_retained_totals_are_reported_with_a_scope() {
    let tight = Limits::new()
        .with_max_work(0)
        .with_max_input_bytes(0)
        .with_max_output_bytes(0)
        .with_max_depth(0)
        .with_max_nodes(0)
        .with_max_storage_bytes(0)
        .with_max_integer_bits(0)
        .with_max_exponent(0)
        .with_max_frames(0);
    let c = plain(tight);
    for &checked in LimitField::ALL {
        let (id, scope, _, _) = limit(c.check(checked, 1));
        assert_eq!(id, field(checked));
        let retained = matches!(checked, LimitField::Nodes | LimitField::StorageBytes);
        assert_eq!(scope, retained.then_some(LimitScope::Value), "{checked:?}");
    }
    let mut c = plain(tight);
    assert_eq!(limit(c.charge(1)).1, None);
    assert_eq!(limit(c.charge_output(1)).1, None);
    let mut c = plain(Limits::new().with_max_frames(0));
    assert_eq!(limit(c.enter_frame()).1, None);
    assert_eq!(limit(c.check_parameter("rows", 0, 1)).1, None);
    for (limits, cost, measure) in [
        (
            Limits::new().with_max_nodes(0),
            Storage::new(1, 0),
            LimitField::Nodes,
        ),
        (
            Limits::new().with_max_storage_bytes(0),
            Storage::new(0, 1),
            LimitField::StorageBytes,
        ),
    ] {
        let mut c = plain(limits);
        for scope in [LimitScope::Value, LimitScope::Frame, LimitScope::Temporary] {
            assert_eq!(
                limit(c.check_storage(cost, scope)).1,
                Some(scope),
                "{measure:?}"
            );
        }
        let (id, scope, _, _) = limit(c.reserve(cost));
        assert_eq!((id, scope), (field(measure), Some(LimitScope::Temporary)));
        let frame = c.enter_frame().unwrap();
        assert_eq!(
            limit(c.set_frame_cost(&frame, cost)),
            (
                field(measure),
                Some(LimitScope::Frame),
                0,
                LimitAmount::Required(1)
            )
        );
        c.leave_frame(frame);
    }
}

#[test]
fn derived_limits_name_their_field_and_parameters_their_name() {
    let mut c = plain(Limits::new().with_max_exponent(256));
    assert_eq!(
        limit(binomial_row(257, &mut c)),
        (
            field(LimitField::Exponent),
            None,
            256,
            LimitAmount::Required(257)
        )
    );
    assert_eq!(c.work_used(), 0);
    assert_eq!(
        limit(c.check_parameter("rows", 10, 11)),
        (
            LimitId::Parameter(String::from("rows")),
            None,
            10,
            LimitAmount::Required(11)
        )
    );
    c.check_parameter("rows", 10, 10).unwrap();
}

// ---------------------------------------------------------------------------
// Reading the clock and the overrun after a deadline

#[test]
fn the_clock_is_read_on_a_fixed_schedule() {
    let clock = FakeClock::at(0);
    let mut c = context(Limits::new(), &clock, &FakeProbe::default()).with_deadline(1_000);
    c.charge(1).unwrap();
    assert_eq!(clock.reads(), 1);
    for _ in 0..POLL_WINDOW - 1 {
        c.charge(LARGE_CHARGE - 1).unwrap();
    }
    assert_eq!(clock.reads(), 1);
    c.charge(1).unwrap();
    assert_eq!(clock.reads(), 2);
    c.charge(0).unwrap();
    assert_eq!(clock.reads(), 3);
    c.charge(LARGE_CHARGE).unwrap();
    assert_eq!(clock.reads(), 4);
    c.charge(1).unwrap();
    assert_eq!(clock.reads(), 5);
    c.charge(1).unwrap();
    assert_eq!(clock.reads(), 5);
    let reserved = c.reserve(Storage::new(1, 1)).unwrap();
    c.release(reserved);
    assert_eq!(clock.reads(), 5);
    // Frame operations poll as charges of one unit: after a reading, 63 of
    // them read no clock and the 64th reads it.
    c.charge(0).unwrap();
    let reads = clock.reads();
    let mut open = None;
    for _ in 0..POLL_WINDOW - 1 {
        match open.take() {
            None => open = Some(c.enter_frame().unwrap()),
            Some(frame) => {
                c.set_frame_cost(&frame, Storage::new(1, 1)).unwrap();
                c.leave_frame(frame);
            }
        }
        assert_eq!(clock.reads(), reads);
    }
    let frame = open.unwrap();
    c.set_frame_cost(&frame, Storage::new(1, 1)).unwrap();
    assert_eq!(clock.reads(), reads + 1);
    c.leave_frame(frame);
}

#[test]
fn without_a_deadline_no_clock_is_read() {
    let clock = FakeClock::at(0);
    let mut c = context(Limits::new(), &clock, &FakeProbe::default());
    for amount in [0, 1, 64, 1_000] {
        c.charge(amount).unwrap();
    }
    c.charge_output(100).unwrap();
    let frame = c.enter_frame().unwrap();
    c.set_frame_cost(&frame, Storage::new(1, 1)).unwrap();
    c.leave_frame(frame);
    assert_eq!(clock.reads(), 0);
}

/// The deadline passes right after the clock reading of a large charge: the
/// work of that charge runs, and the next charge reads the clock and fails.
/// The overrun is the large amount, within the bound of the contract.
#[test]
fn a_deadline_right_after_a_large_charge_reading_overruns_by_at_most_the_bound() {
    for large in [LARGE_CHARGE, 1_000, 50_000] {
        let clock = FakeClock::at(99);
        let mut c = context(Limits::new(), &clock, &FakeProbe::default()).with_deadline(100);
        c.charge(1).unwrap();
        c.charge(large).unwrap();
        clock.set(100);
        let at_deadline = c.work_used() - large;
        let mut passed = 0;
        while c.charge(1).is_ok() {
            passed += 1;
            assert!(passed < 10_000, "the deadline was never observed");
        }
        assert_eq!(passed, 0);
        let overrun = c.work_used() - at_deadline;
        assert_eq!(overrun, large);
        assert!(overrun <= overrun_bound(large));
        assert_eq!(kind(c.charge(0)), Some(ErrorKind::DeadlineExceeded));
        assert_eq!(kind(c.enter_frame()), Some(ErrorKind::DeadlineExceeded));
    }
}

/// The deadline passes right after the reading of a small charge: that
/// charge and at most 63 small charges after it run.
#[test]
fn a_deadline_right_after_a_small_charge_reading_overruns_by_at_most_the_bound() {
    let clock = FakeClock::at(99);
    let mut c = context(Limits::new(), &clock, &FakeProbe::default()).with_deadline(100);
    c.charge(LARGE_CHARGE - 1).unwrap();
    clock.set(100);
    let mut passed = 0;
    while c.charge(LARGE_CHARGE - 1).is_ok() {
        passed += 1;
    }
    assert_eq!(passed, POLL_WINDOW - 1);
    let overrun = c.work_used();
    assert_eq!(overrun, u64::from(POLL_WINDOW) * (LARGE_CHARGE - 1));
    assert_eq!(overrun, overrun_bound(0));
}

/// The deadline passes right after a reading, and then only frames are
/// entered and left: the 64th frame operation observes the expiry.
#[test]
fn frame_operations_alone_observe_a_deadline_within_the_bound() {
    let clock = FakeClock::at(99);
    let mut c = context(Limits::new(), &clock, &FakeProbe::default()).with_deadline(100);
    c.charge(1).unwrap();
    clock.set(100);
    let mut passed = 0;
    loop {
        match c.enter_frame() {
            Ok(frame) => {
                c.leave_frame(frame);
                passed += 1;
            }
            Err(error) => {
                assert_eq!(error.kind(), ErrorKind::DeadlineExceeded);
                break;
            }
        }
        assert!(passed < 10_000, "the deadline was never observed");
    }
    assert_eq!(passed, POLL_WINDOW - 1);
    assert_eq!(c.work_used(), u64::from(POLL_WINDOW));
    assert!(c.work_used() <= overrun_bound(1));
}

// ---------------------------------------------------------------------------
// Bounded output

fn serialize(chunks: &[&str], context: &mut Context, out: &mut Vec<u8>) -> Result<()> {
    for chunk in chunks {
        context.charge_output(chunk.len() as u64)?;
    }
    for chunk in chunks {
        out.extend_from_slice(chunk.as_bytes());
    }
    Ok(())
}

#[test]
fn output_bytes_are_charged_and_an_overflow_leaves_no_output() {
    let mut c = plain(Limits::new().with_max_output_bytes(10));
    let mut out = Vec::new();
    serialize(&["x^2", "+1"], &mut c, &mut out).unwrap();
    assert_eq!(out, b"x^2+1");
    assert_eq!((c.output_used(), c.work_used()), (5, 5));
    let mut more = Vec::new();
    assert_eq!(
        kind(serialize(&["123", "456"], &mut c, &mut more)),
        Some(ErrorKind::ResourceLimit)
    );
    assert!(more.is_empty());
    assert_eq!(c.output_used(), 8);
    assert_eq!(
        limit(c.charge_output(6)),
        (
            field(LimitField::OutputBytes),
            None,
            10,
            LimitAmount::Required(14)
        )
    );
    // Output also charges the work, which may run out first.
    let mut short = plain(Limits::new().with_max_work(3));
    assert_eq!(limit(short.charge_output(4)).0, field(LimitField::Work));
    assert_eq!(short.output_used(), 0);
}

// ---------------------------------------------------------------------------
// Frames and temporaries

/// The frame-cost check and the temporary check bound the same totals; the
/// scope tells them apart, for nodes and for bytes alike, and a rejected
/// frame cost is not charged.
#[test]
fn frame_cost_and_temporary_limits_are_told_apart_by_scope() {
    for (limits, cost, measure) in [
        (
            Limits::new().with_max_nodes(10),
            Storage::new(5, 0),
            LimitField::Nodes,
        ),
        (
            Limits::new().with_max_storage_bytes(10),
            Storage::new(0, 5),
            LimitField::StorageBytes,
        ),
    ] {
        let mut c = plain(limits);
        let outer = c.enter_frame().unwrap();
        let kept = Storage::new(cost.nodes * 6 / 5, cost.bytes * 6 / 5);
        c.set_frame_cost(&outer, kept).unwrap();
        let inner = c.enter_frame().unwrap();
        let work = c.work_used();
        let at_frame = exceeded(c.set_frame_cost(&inner, cost)).unwrap();
        assert_eq!(c.work_used(), work);
        assert_eq!(c.frame_cost(&inner), Some(Storage::ZERO));
        let at_temporary = exceeded(c.reserve(cost)).unwrap();
        assert_eq!(c.retained(), kept);
        assert_eq!(at_frame.id(), &field(measure));
        assert_eq!(at_temporary.id(), &field(measure));
        assert_eq!(at_frame.scope(), Some(LimitScope::Frame));
        assert_eq!(at_temporary.scope(), Some(LimitScope::Temporary));
        assert_eq!(
            (at_frame.allowed(), at_frame.amount()),
            (10, LimitAmount::Required(11))
        );
        assert_ne!(at_frame, at_temporary);
        c.leave_frame(inner);
        c.leave_frame(outer);
    }
}

/// The byte limit is reached while the nodes are far below theirs, and the
/// node limit while the bytes are; when both are exceeded, nodes are
/// reported.
#[test]
fn storage_bytes_and_nodes_are_reached_independently() {
    let mut c = plain(
        Limits::new()
            .with_max_nodes(1_000_000)
            .with_max_storage_bytes(100),
    );
    assert_eq!(
        limit(c.check_storage(Storage::new(1, 131), LimitScope::Value)),
        (
            field(LimitField::StorageBytes),
            Some(LimitScope::Value),
            100,
            LimitAmount::Required(131)
        )
    );
    let held = c.reserve(Storage::new(20, 100)).unwrap();
    assert_eq!(c.retained(), Storage::new(20, 100));
    assert_eq!(
        limit(c.reserve(Storage::new(0, 1))).0,
        field(LimitField::StorageBytes)
    );
    c.release(held);

    let c = plain(
        Limits::new()
            .with_max_nodes(3)
            .with_max_storage_bytes(1 << 40),
    );
    c.check_storage(Storage::new(3, 11), LimitScope::Value)
        .unwrap();
    assert_eq!(
        limit(c.check_storage(Storage::new(5, 20), LimitScope::Value)),
        (
            field(LimitField::Nodes),
            Some(LimitScope::Value),
            3,
            LimitAmount::Required(5)
        )
    );
    let mut both = plain(Limits::new().with_max_nodes(1).with_max_storage_bytes(1));
    assert_eq!(
        limit(both.reserve(Storage::new(2, 2))).0,
        field(LimitField::Nodes)
    );
}

/// A count checked through `check` counts the open frames and the reserved
/// temporaries, with the scope `Value`, as `check_storage` does.
#[test]
fn check_on_the_retained_totals_counts_frames_and_temporaries() {
    let mut c = plain(Limits::new().with_max_nodes(10).with_max_storage_bytes(10));
    let frame = c.enter_frame().unwrap();
    c.set_frame_cost(&frame, Storage::new(4, 4)).unwrap();
    let held = c.reserve(Storage::new(3, 3)).unwrap();
    c.check(LimitField::Nodes, 3).unwrap();
    c.check(LimitField::StorageBytes, 3).unwrap();
    let nodes = limit(c.check(LimitField::Nodes, 4));
    assert_eq!(
        nodes,
        (
            field(LimitField::Nodes),
            Some(LimitScope::Value),
            10,
            LimitAmount::Required(11)
        )
    );
    assert_eq!(
        nodes,
        limit(c.check_storage(Storage::new(4, 0), LimitScope::Value))
    );
    assert_eq!(
        limit(c.check(LimitField::StorageBytes, 4)),
        limit(c.check_storage(Storage::new(0, 4), LimitScope::Value))
    );
    c.release(held);
    c.leave_frame(frame);
}

#[test]
fn frame_costs_and_temporaries_are_checked_together_and_restored() {
    let mut c = plain(Limits::new().with_max_nodes(20).with_max_storage_bytes(40));
    let outer = c.enter_frame().unwrap();
    c.set_frame_cost(&outer, Storage::new(3, 5)).unwrap();
    let first = c.reserve(Storage::new(2, 7)).unwrap();
    let second = c.reserve(Storage::new(4, 11)).unwrap();
    c.check_storage(Storage::new(11, 17), LimitScope::Value)
        .unwrap();
    assert!(
        c.check_storage(Storage::new(12, 17), LimitScope::Value)
            .is_err()
    );
    assert!(
        c.check_storage(Storage::new(11, 18), LimitScope::Value)
            .is_err()
    );
    let inner = c.enter_frame().unwrap();
    assert_eq!(
        limit(c.set_frame_cost(&inner, Storage::new(12, 0))).1,
        Some(LimitScope::Frame)
    );
    c.set_frame_cost(&inner, Storage::new(11, 17)).unwrap();
    // Recording a cost again replaces it.
    c.set_frame_cost(&inner, Storage::new(1, 1)).unwrap();
    assert_eq!(c.retained(), Storage::new(10, 24));
    // Any open frame may be given a cost, not only the innermost.
    c.set_frame_cost(&outer, Storage::new(2, 2)).unwrap();
    assert_eq!(c.frame_cost(&outer), Some(Storage::new(2, 2)));
    assert_eq!(c.retained(), Storage::new(9, 21));
    c.release(second);
    c.release(first);
    // Leaving the outer frame closes the inner one too.
    c.leave_frame(outer);
    assert_eq!((c.open_frames(), c.retained()), (0, Storage::ZERO));
    let work = c.work_used();
    c.set_frame_cost(&inner, Storage::new(1_000, 1_000))
        .unwrap();
    assert_eq!(c.work_used(), work + 1);
    assert_eq!(c.retained(), Storage::ZERO);
    c.leave_frame(inner);
    assert_eq!(c.open_frames(), 0);
}

#[test]
fn a_zero_reservation_succeeds_at_the_limit() {
    let mut c = plain(Limits::new().with_max_nodes(5));
    let frame = c.enter_frame().unwrap();
    c.set_frame_cost(&frame, Storage::new(5, 0)).unwrap();
    let zero = c.reserve(Storage::ZERO).unwrap();
    assert_eq!(zero.cost(), Storage::ZERO);
    assert!(c.reserve(Storage::new(1, 0)).is_err());
    c.release(zero);
    c.leave_frame(frame);
}

// ---------------------------------------------------------------------------
// Sub-computations share the context of their caller

#[test]
fn sub_computations_share_the_context_of_their_caller() {
    let go = |sizes: &[u64]| {
        let clock = FakeClock::at(0);
        let limits = Limits::new().with_max_work(5_000).with_max_frames(100);
        let mut c = context(limits, &clock, &FakeProbe::default()).with_deadline(u64::MAX);
        let held = c.reserve(Storage::new(10, 10)).unwrap();
        let mut rows = Vec::new();
        for &n in sizes {
            rows.push(binomial_row(n, &mut c).ok());
            assert_eq!(c.retained(), Storage::new(10, 10));
        }
        c.release(held);
        (rows, c.work_used(), clock.reads())
    };
    let sizes = [10, 30, 40];
    let first = go(&sizes);
    assert_eq!(go(&sizes), first);
    assert!(first.0.iter().all(Option::is_some));
    assert_eq!(first.1, row_work(10) + row_work(30) + row_work(40));
}

/// Without sub-budgets, the order of the parts decides which part fails, and
/// every failure names `max_work`.
#[test]
fn without_sub_budgets_the_failing_part_depends_on_the_order() {
    let total = row_work(30) + row_work(10);
    let failing = |sizes: &[u64]| {
        let mut c = plain(Limits::new().with_max_work(total).with_max_frames(100));
        let mut failed = Vec::new();
        for &n in sizes {
            if let Err(error) = binomial_row(n, &mut c) {
                assert_eq!(
                    error.exceeded().map(LimitExceeded::id),
                    Some(&field(LimitField::Work))
                );
                failed.push(n);
            }
        }
        (failed, c.work_used())
    };
    assert_eq!(failing(&[30, 10, 20]), (vec![20], total));
    assert_eq!(failing(&[20, 10, 30]), (vec![30], total));
    assert_eq!(failing(&[30, 20, 10]), (vec![20, 10], total));
}

// ---------------------------------------------------------------------------
// Carried over from the tests of the earlier implementation

// Carried over: charges accumulate within the budget.
#[test]
fn ex1_charges_accumulate_within_the_budget() {
    let mut context = budget(10);
    context.charge(4).unwrap();
    context.charge(6).unwrap();
    assert_eq!(context.work_used(), 10);
}

// Carried over: an exhausted budget is a resource limit naming `max_work`.
#[test]
fn ex2_exhausted_budget_is_a_resource_error() {
    let mut context = budget(10);
    context.charge(8).unwrap();
    let error = context.charge(3).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::ResourceLimit);
    assert_eq!(error.exceeded().unwrap().id(), &field(LimitField::Work));
    assert_eq!(context.work_used(), 8);
}

// Carried over: cancellation is shared by the clones of the flag.
#[test]
fn ex3_cancellation_is_shared_by_clones_of_the_flag() {
    let flag = CancelFlag::new();
    let mut context = Context::new(Limits::new(), flag.clone());
    context.charge(1).unwrap();
    flag.cancel();
    assert_eq!(kind(context.charge(0)), Some(ErrorKind::Cancelled));
}

// Carried over: an expired deadline stops work. The deadline is the current
// reading of the monotonic clock, so it has passed at the first charge.
#[test]
fn ex4_expired_deadline_stops_work() {
    let mut context = budget(100_000).with_timeout(0);
    assert_eq!(kind(context.charge(1)), Some(ErrorKind::DeadlineExceeded));
}

// Carried over: a zero charge polls without consuming work.
#[test]
fn ex5_zero_charge_polls_without_consuming_work() {
    let mut context = budget(1);
    context.charge(0).unwrap();
    context.charge(0).unwrap();
    assert_eq!(context.work_used(), 0);
}

// Carried over: cancellation takes priority over an exhausted budget.
#[test]
fn cancellation_takes_priority_over_an_exhausted_budget() {
    let flag = CancelFlag::new();
    let mut context = Context::new(Limits::new().with_max_work(0), flag.clone());
    flag.cancel();
    assert_eq!(kind(context.charge(1)), Some(ErrorKind::Cancelled));
}

// Carried over, with a fake clock in place of a sleep: an expired deadline
// takes priority over an exhausted budget, even when the small charge that
// exhausts it is not due to read the clock.
#[test]
fn expired_deadline_takes_priority_over_an_exhausted_budget() {
    let clock = FakeClock::at(0);
    let mut context = context(
        Limits::new().with_max_work(4),
        &clock,
        &FakeProbe::default(),
    )
    .with_deadline(20);
    context.charge(1).unwrap();
    clock.set(40);
    assert_eq!(kind(context.charge(10)), Some(ErrorKind::DeadlineExceeded));
}

// Carried over: an observed expiry is final.
#[test]
fn observed_expiry_is_final() {
    let mut context = budget(100_000).with_timeout(0);
    assert!(context.charge(0).is_err());
    for _ in 0..100 {
        assert_eq!(kind(context.charge(1)), Some(ErrorKind::DeadlineExceeded));
    }
}

// Carried over, with charges in place of parsing and polynomial conversion:
// a cancellation from another thread stops the request at its next charge,
// and an unrelated request runs on.
#[test]
fn cancellation_is_shared_but_does_not_cancel_unrelated_requests() {
    let flag = CancelFlag::new();
    let mut context = Context::new(Limits::new(), flag.clone());
    context.charge(5).unwrap();
    std::thread::spawn(move || flag.cancel()).join().unwrap();
    assert_eq!(kind(context.charge(5)), Some(ErrorKind::Cancelled));
    let mut unrelated = Context::new(Limits::new(), CancelFlag::new());
    unrelated.charge(5).unwrap();
    assert_eq!(kind(context.charge(1)), Some(ErrorKind::Cancelled));
}

// Carried over: the exact budget is accepted at the `u64` width, and one unit
// more is rejected.
#[test]
fn exact_budget_is_accepted_and_overflow_rejected() {
    let mut context = budget(u64::MAX);
    context.charge(u64::MAX).unwrap();
    assert_eq!(kind(context.charge(1)), Some(ErrorKind::ResourceLimit));
    assert_eq!(context.work_used(), u64::MAX);
}

// Carried over: a far deadline does not interfere.
#[test]
fn far_deadline_does_not_interfere() {
    let mut context = budget(1_000).with_timeout(3_600_000_000_000);
    for _ in 0..1_000 {
        context.charge(1).unwrap();
    }
    assert_eq!(context.work_used(), 1_000);
}

// ---------------------------------------------------------------------------
// Host tests: the default clock and cancellation flag

/// Two evaluations on one context, with the default clock and flag: another
/// thread cancels the flag between them, and the second evaluation fails at
/// its first charge, with the work of the first kept.
#[test]
fn host_cancelled_between_two_evaluations() {
    let flag = CancelFlag::new();
    let limits = Limits::new().with_max_frames(100);
    let mut context = Context::new(limits, flag.clone()).with_timeout(3_600_000_000_000);
    let first = binomial_row(20, &mut context).unwrap();
    assert_eq!(first[10], 184_756);
    let work = context.work_used();
    assert_eq!(work, row_work(20));
    let remote = flag.clone();
    std::thread::spawn(move || remote.cancel()).join().unwrap();
    let second = binomial_row(20, &mut context);
    assert_eq!(kind(second), Some(ErrorKind::Cancelled));
    assert_eq!(context.work_used(), work);
    assert_eq!(context.open_frames(), 0);
}

/// A real deadline of one millisecond on the monotonic clock passes while the
/// request keeps charging: zero charges read the clock each time, so the
/// expiry is observed, and an evaluation after it fails at once.
#[test]
fn host_deadline_expires() {
    let mut context = Context::new(Limits::new(), CancelFlag::new()).with_timeout(1_000_000);
    let mut polls = 0_u64;
    let error = loop {
        match context.charge(0) {
            Ok(()) => polls += 1,
            Err(error) => break error,
        }
        assert!(polls < 1_000_000_000, "the deadline was never observed");
    };
    assert_eq!(error.kind(), ErrorKind::DeadlineExceeded);
    assert_eq!(context.work_used(), 0);
    assert_eq!(
        kind(binomial_row(3, &mut context)),
        Some(ErrorKind::DeadlineExceeded)
    );
}
