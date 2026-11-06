//! Unit tests of the context, carried over from the earlier implementation
//! where they apply. The clock and the cancellation probe are fakes injected
//! through the context, so no test depends on the speed of a clock and no
//! test hook runs inside charging.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Barrier};

use super::*;
use crate::ErrorKind;

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

/// A probe that counts its polls and, when `cancel_at` is set, cancels the
/// shared `flag` just before that poll reads it.
#[derive(Clone)]
struct FakeProbe {
    flag: CancelFlag,
    polls: Arc<AtomicU64>,
    cancel_at: Option<u64>,
}

impl FakeProbe {
    fn new() -> Self {
        Self {
            flag: CancelFlag::new(),
            polls: Arc::new(AtomicU64::new(0)),
            cancel_at: None,
        }
    }

    fn cancelling_at(flag: &CancelFlag, poll: u64) -> Self {
        Self {
            flag: flag.clone(),
            polls: Arc::new(AtomicU64::new(0)),
            cancel_at: Some(poll),
        }
    }

    fn polls(&self) -> u64 {
        self.polls.load(Ordering::SeqCst)
    }
}

impl CancelProbe for FakeProbe {
    fn is_cancelled(&mut self) -> bool {
        let poll = self.polls.fetch_add(1, Ordering::SeqCst) + 1;
        if self.cancel_at == Some(poll) {
            self.flag.cancel();
        }
        self.flag.is_cancelled()
    }

    fn fork(&self) -> Box<dyn CancelProbe> {
        Box::new(self.clone())
    }
}

fn context(limits: Limits, clock: &FakeClock, probe: &FakeProbe) -> Context {
    Context::with_observers(limits, Box::new(clock.clone()), Box::new(probe.clone()))
}

fn work(max_work: u64, clock: &FakeClock) -> Context {
    context(
        Limits::new().with_max_work(max_work),
        clock,
        &FakeProbe::new(),
    )
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

// Carried over, adapted: reservations nest exactly, every check counts the
// open frame and every reservation, and releasing restores the totals. A
// reservation charges no work.
#[test]
fn reservation_nesting_is_exact_and_release_restores() {
    let mut c = context(
        Limits::new().with_max_nodes(20).with_max_storage_bytes(40),
        &FakeClock::at(0),
        &FakeProbe::new(),
    );
    let frame = c.enter_frame().unwrap();
    c.set_frame_cost(&frame, Storage::new(3, 5)).unwrap();
    let work = c.work_used();
    let outer = c.reserve(Storage::new(2, 7)).unwrap();
    assert_eq!(c.temporaries, Storage::new(2, 7));
    let inner = c.reserve(Storage::new(4, 11)).unwrap();
    assert_eq!(c.temporaries, Storage::new(6, 18));
    assert!(
        c.check_storage(Storage::new(11, 17), LimitScope::Value)
            .is_ok()
    );
    assert!(
        c.check_storage(Storage::new(12, 17), LimitScope::Value)
            .is_err()
    );
    assert!(
        c.check_storage(Storage::new(11, 18), LimitScope::Value)
            .is_err()
    );
    c.release(inner);
    assert_eq!(c.temporaries, Storage::new(2, 7));
    c.release(outer);
    assert_eq!(c.temporaries, Storage::ZERO);
    assert_eq!(c.work_used(), work);
    assert_eq!(c.open_frames(), 1);
    assert!(
        c.check_storage(Storage::new(17, 35), LimitScope::Value)
            .is_ok()
    );
    c.leave_frame(frame);
}

// Carried over, adapted: a zero reservation leaves the charges and the
// failures of the same computation unchanged, for every budget.
#[test]
fn an_empty_reservation_preserves_charges_and_failures() {
    let steps = |c: &mut Context| -> Result<()> {
        c.charge(3)?;
        c.check_storage(Storage::new(1, 8), LimitScope::Value)?;
        c.charge(5)
    };
    for budget in 0..=8 {
        let clock = FakeClock::at(0);
        let mut plain = work(budget, &clock);
        let mut scoped = work(budget, &clock);
        let without = steps(&mut plain);
        let zero = scoped.reserve(Storage::ZERO).unwrap();
        let with = steps(&mut scoped);
        scoped.release(zero);
        assert_eq!(kind(without.clone()), kind(with.clone()), "{budget}");
        assert_eq!(exceeded(without), exceeded(with), "{budget}");
        assert_eq!(plain.work_used(), scoped.work_used());
        assert_eq!(scoped.retained(), Storage::ZERO);
    }
}

// Carried over, adapted from nested commands to frames: leaving restores the
// frames open before entering.
#[test]
fn leaving_restores_the_frames_open_before_entering() {
    let mut c = work(100, &FakeClock::at(0));
    let outer = c.enter_frame().unwrap();
    let inner = c.enter_frame().unwrap();
    assert_eq!(c.open_frames(), 2);
    c.leave_frame(inner);
    assert_eq!(c.open_frames(), 1);
    c.leave_frame(outer);
    assert_eq!(c.open_frames(), 0);
    assert_eq!(c.work_used(), 2);
}

// Carried over, adapted from nested commands to frames: entering at the
// limit fails without changing the frames, and, unlike the source, without
// charging.
#[test]
fn entering_at_max_frames_fails_without_changing_the_frames() {
    for limit in [8, 3, 0] {
        let mut c = context(
            Limits::new().with_max_frames(limit),
            &FakeClock::at(0),
            &FakeProbe::new(),
        );
        let mut frames = Vec::new();
        for _ in 0..limit {
            frames.push(c.enter_frame().unwrap());
        }
        let refused = exceeded(c.enter_frame()).unwrap();
        assert_eq!(refused.id(), &LimitId::Field(LimitField::Frames));
        assert_eq!(refused.scope(), None);
        assert_eq!(refused.amount(), LimitAmount::Required(limit + 1));
        assert_eq!(c.open_frames(), limit);
        assert_eq!(c.work_used(), limit);
    }
}

// Carried over, adapted from leaving at depth zero: a token whose frame was
// closed changes nothing, even when a new frame took its place.
#[test]
fn a_closed_frame_token_changes_nothing() {
    let mut c = work(100, &FakeClock::at(0));
    let first = c.enter_frame().unwrap();
    let stale = c.enter_frame().unwrap();
    c.leave_frame(first);
    assert_eq!(c.open_frames(), 0);
    let again = c.enter_frame().unwrap();
    let reused = c.enter_frame().unwrap();
    assert_eq!((reused.index, stale.index), (1, 1));
    assert_eq!(c.frame_cost(&stale), None);
    let before = c.work_used();
    c.set_frame_cost(&stale, Storage::new(1_000, 1_000))
        .unwrap();
    assert_eq!(c.work_used(), before + 1);
    assert_eq!(c.frame_cost(&reused), Some(Storage::ZERO));
    assert_eq!(c.retained(), Storage::ZERO);
    c.leave_frame(stale);
    assert_eq!(c.open_frames(), 2);
    c.leave_frame(again);
    assert_eq!(c.open_frames(), 0);
}

// Carried over: an expired deadline stops the first charge, whatever its
// amount, and an observed expiry is final: a later reading before the
// deadline does not lift it, and no further reading is made.
#[test]
fn an_expired_deadline_stops_the_first_charge_and_stays_final() {
    for amount in [0, 1, 63, 64, 1000] {
        let clock = FakeClock::at(200);
        let mut c = work(10_000, &clock).with_deadline(100);
        assert_eq!(kind(c.charge(amount)), Some(ErrorKind::DeadlineExceeded));
        assert_eq!(c.work_used(), 0);
        assert_eq!(clock.reads(), 1);
        clock.set(0);
        assert_eq!(kind(c.charge(1)), Some(ErrorKind::DeadlineExceeded));
        assert_eq!(kind(c.charge(0)), Some(ErrorKind::DeadlineExceeded));
        assert_eq!(clock.reads(), 1);
        // Setting a deadline again lifts the observed expiry.
        let mut c = c.with_deadline(100);
        c.charge(1).unwrap();
        assert_eq!(clock.reads(), 2);
    }
}

// A timeout reads the clock once, when it is set, and the deadline is that
// reading plus the timeout.
#[test]
fn a_timeout_counts_from_one_reading_of_the_clock() {
    let clock = FakeClock::at(1_000);
    let mut c = work(10_000, &clock).with_timeout(10);
    assert_eq!(clock.reads(), 1);
    c.charge(1).unwrap();
    assert_eq!(clock.reads(), 2);
    clock.set(1_009);
    c.charge(0).unwrap();
    clock.set(1_010);
    assert_eq!(kind(c.charge(0)), Some(ErrorKind::DeadlineExceeded));
    assert_eq!(clock.reads(), 4);
}

// Carried over: setting a new deadline reads the clock at the next charge.
#[test]
fn replacing_the_deadline_reads_the_clock_on_the_next_charge() {
    let clock = FakeClock::at(0);
    let mut c = work(10_000, &clock).with_deadline(1_000_000);
    for _ in 0..10 {
        c.charge(1).unwrap();
    }
    let mut c = c.with_deadline(0);
    assert_eq!(kind(c.charge(1)), Some(ErrorKind::DeadlineExceeded));
    assert_eq!(c.work_used(), 10);
}

// Carried over: exactly 63 small charges may pass after a reading before the
// clock is read again.
#[test]
fn small_charges_are_bounded_between_clock_reads() {
    let clock = FakeClock::at(0);
    let mut c = work(10_000, &clock).with_deadline(100);
    c.charge(1).unwrap();
    clock.set(200);
    for _ in 0..POLL_WINDOW - 1 {
        c.charge(LARGE_CHARGE - 1).unwrap();
    }
    assert_eq!(kind(c.charge(1)), Some(ErrorKind::DeadlineExceeded));
    assert_eq!(
        c.work_used(),
        1 + u64::from(POLL_WINDOW - 1) * (LARGE_CHARGE - 1)
    );
}

// Carried over: zero and large charges read the clock at once.
#[test]
fn zero_and_large_charges_read_the_clock_immediately() {
    for amount in [0, LARGE_CHARGE, LARGE_CHARGE + 1, 5000] {
        let clock = FakeClock::at(0);
        let mut c = work(10_000, &clock).with_deadline(100);
        c.charge(1).unwrap();
        clock.set(200);
        assert_eq!(
            kind(c.charge(amount)),
            Some(ErrorKind::DeadlineExceeded),
            "{amount}"
        );
        assert_eq!(c.work_used(), 1);
    }
}

// Carried over, adapted to the rewritten reading rule: a zero charge starts a
// new window of 63 small charges; a large charge leaves no window, so the
// charge after it reads the clock and starts one.
#[test]
fn every_clock_read_restarts_the_interval() {
    let clock = FakeClock::at(0);
    let mut c = work(1_000_000, &clock).with_deadline(100);
    c.charge(1).unwrap();
    for _ in 0..40 {
        c.charge(1).unwrap();
    }
    assert_eq!(clock.reads(), 1);
    c.charge(0).unwrap();
    assert_eq!((clock.reads(), c.credit), (2, POLL_WINDOW - 1));
    for _ in 0..40 {
        c.charge(1).unwrap();
    }
    c.charge(LARGE_CHARGE).unwrap();
    assert_eq!((clock.reads(), c.credit), (3, 0));
    c.charge(1).unwrap();
    assert_eq!((clock.reads(), c.credit), (4, POLL_WINDOW - 1));
    clock.set(200);
    for _ in 0..POLL_WINDOW - 1 {
        c.charge(1).unwrap();
    }
    assert_eq!(kind(c.charge(1)), Some(ErrorKind::DeadlineExceeded));
}

// Carried over: an expiry that the polling step did not read still takes
// precedence over exhausted work, since exhaustion reads the clock once more.
#[test]
fn an_unobserved_expiry_still_precedes_work_exhaustion() {
    let clock = FakeClock::at(0);
    let mut c = work(5, &clock).with_deadline(100);
    c.charge(1).unwrap();
    clock.set(200);
    assert_eq!(kind(c.charge(5)), Some(ErrorKind::DeadlineExceeded));
    assert_eq!(c.work_used(), 1);
    assert_eq!(kind(c.charge(1)), Some(ErrorKind::DeadlineExceeded));

    let live_clock = FakeClock::at(0);
    let mut live = work(5, &live_clock).with_deadline(100);
    live.charge(1).unwrap();
    assert_eq!(kind(live.charge(5)), Some(ErrorKind::ResourceLimit));
    assert_eq!(live.work_used(), 1);
}

// Carried over: cancellation precedes an expired deadline, and a cancelled
// charge reads no clock.
#[test]
fn cancellation_precedes_an_expired_deadline() {
    let clock = FakeClock::at(200);
    let probe = FakeProbe::new();
    let mut c = context(Limits::new(), &clock, &probe).with_deadline(100);
    probe.flag.cancel();
    assert_eq!(kind(c.charge(1)), Some(ErrorKind::Cancelled));
    assert_eq!(kind(c.charge(0)), Some(ErrorKind::Cancelled));
    assert_eq!(clock.reads(), 0);
}

// Carried over: without a deadline no clock is read, and charging is plain
// accounting.
#[test]
fn contexts_without_a_deadline_are_unchanged() {
    let clock = FakeClock::at(0);
    let mut c = work(100, &clock);
    for _ in 0..100 {
        c.charge(1).unwrap();
    }
    assert_eq!((c.work_used(), c.credit, c.expired), (100, 0, false));
    assert_eq!(kind(c.charge(1)), Some(ErrorKind::ResourceLimit));
    c.charge(0).unwrap();
    assert_eq!(clock.reads(), 0);
}

// Carried over, adapted: cancelling the shared flag just before the third
// poll is observed by that poll, through the real flag.
#[test]
fn a_selected_poll_reads_the_shared_cancellation_flag() {
    let flag = CancelFlag::new();
    let probe = FakeProbe::cancelling_at(&flag, 3);
    let mut c = context(Limits::new(), &FakeClock::at(0), &probe);
    c.charge(1).unwrap();
    c.charge(2).unwrap();
    assert_eq!(kind(c.charge(4)), Some(ErrorKind::Cancelled));
    assert_eq!(c.work_used(), 3);
    assert_eq!(probe.polls(), 3);
    assert!(flag.is_cancelled());
}

// Carried over, adapted: charges of other contexts, on this thread or
// another, poll their own probes and never this one.
#[test]
fn other_contexts_and_threads_do_not_consume_polls() {
    let flag = CancelFlag::new();
    let probe = FakeProbe::cancelling_at(&flag, 2);
    let mut c = context(Limits::new(), &FakeClock::at(0), &probe);
    let mut other = context(Limits::new(), &FakeClock::at(0), &FakeProbe::new());
    other.charge(7).unwrap();
    let shared = flag.clone();
    std::thread::spawn(move || {
        let mut remote = Context::new(Limits::new(), shared);
        remote.charge(9).unwrap();
    })
    .join()
    .unwrap();
    c.charge(2).unwrap();
    assert_eq!(kind(c.charge(4)), Some(ErrorKind::Cancelled));
    assert_eq!(c.work_used(), 2);
    assert_eq!(probe.polls(), 2);
}

// Carried over, adapted: contexts on two threads at once keep their own
// counts of polls.
#[test]
fn simultaneous_probes_keep_independent_poll_counts() {
    let barrier = Barrier::new(2);
    std::thread::scope(|scope| {
        for poll in [2_u64, 3] {
            let barrier = &barrier;
            scope.spawn(move || {
                let flag = CancelFlag::new();
                let probe = FakeProbe::cancelling_at(&flag, poll);
                let mut c = context(Limits::new(), &FakeClock::at(0), &probe);
                barrier.wait();
                for _ in 1..poll {
                    c.charge(1).unwrap();
                }
                assert_eq!(kind(c.charge(4)), Some(ErrorKind::Cancelled));
                assert_eq!(c.work_used(), poll - 1);
            });
        }
    });
}

// Carried over, adapted: the clock passes the deadline after selected work;
// the zero charge after it reads the clock and observes the expiry, and the
// charges of another context read only their own clock.
#[test]
fn an_expiry_after_selected_work_is_read_and_other_contexts_are_unaffected() {
    let clock = FakeClock::at(0);
    let mut c = work(100_000, &clock).with_deadline(100);
    let other_clock = FakeClock::at(0);
    let mut other = work(100_000, &other_clock).with_deadline(100);
    other.charge(100).unwrap();
    c.charge(3).unwrap();
    clock.set(100);
    assert_eq!(kind(c.charge(0)), Some(ErrorKind::DeadlineExceeded));
    assert_eq!(c.work_used(), 3);
    assert_eq!(clock.reads(), 2);
    assert_eq!(other_clock.reads(), 1);
    other.charge(0).unwrap();
}

// The request failures of a charge, a field check and a storage check carry
// the span that the caller gave, and their order is cancellation, deadline,
// limit.
#[test]
fn request_failures_carry_the_span_of_the_caller() {
    let span = Span::new(2, 5);
    let clock = FakeClock::at(0);
    let probe = FakeProbe::new();
    let mut c = context(Limits::new().with_max_work(1), &clock, &probe).with_deadline(100);
    let error = c.charge_at(2, span).unwrap_err();
    assert_eq!(
        (error.kind(), error.span()),
        (ErrorKind::ResourceLimit, span)
    );
    let error = c.check_at(LimitField::Depth, 129, span).unwrap_err();
    assert_eq!(
        (error.kind(), error.span()),
        (ErrorKind::ResourceLimit, span)
    );
    let error = c
        .check_storage_at(Storage::new(8193, 0), LimitScope::Value, span)
        .unwrap_err();
    assert_eq!(
        (error.kind(), error.span()),
        (ErrorKind::ResourceLimit, span)
    );
    clock.set(100);
    let error = c.charge_at(0, span).unwrap_err();
    assert_eq!(
        (error.kind(), error.span()),
        (ErrorKind::DeadlineExceeded, span)
    );
    probe.flag.cancel();
    let error = c.charge_at(0, span).unwrap_err();
    assert_eq!((error.kind(), error.span()), (ErrorKind::Cancelled, span));
    assert_eq!(c.charge(0).unwrap_err().span(), None);
}

// The invariants of the frame table hold through entering, recording,
// reserving and leaving: frames_total is the sum of the costs in the table,
// and the generation of the next frame never exceeds the work charged.
#[test]
fn frames_total_is_the_sum_of_the_frame_costs() {
    let mut c = work(1_000, &FakeClock::at(0));
    let check = |c: &Context| {
        let mut sum = Storage::ZERO;
        if let Some(frames) = &c.frames {
            for entry in frames.iter() {
                sum = sum.saturating_add(entry.cost);
            }
        }
        assert_eq!(sum, c.frames_total);
        assert!(c.entered <= c.work_used());
    };
    let a = c.enter_frame().unwrap();
    c.set_frame_cost(&a, Storage::new(2, 3)).unwrap();
    check(&c);
    let b = c.enter_frame().unwrap();
    c.set_frame_cost(&b, Storage::new(5, 7)).unwrap();
    c.set_frame_cost(&a, Storage::new(1, 1)).unwrap();
    check(&c);
    let held = c.reserve(Storage::new(4, 4)).unwrap();
    let d = c.enter_frame().unwrap();
    c.set_frame_cost(&d, Storage::new(3, 3)).unwrap();
    check(&c);
    c.leave_frame(b);
    check(&c);
    assert_eq!(c.frames_total, Storage::new(1, 1));
    c.release(held);
    c.leave_frame(a);
    check(&c);
    assert_eq!(c.retained(), Storage::ZERO);
    c.leave_frame(d);
    check(&c);
}
