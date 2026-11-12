//! The checks of work accounting and cancellation of the tool.
//!
//! An operation is checked on fixed inputs, as a run on a context. A run
//! with the budget `MEASURE_WORK`, which it must not exhaust, measures its
//! outcome and its work $w$. The work check then tries budgets below and
//! above $w$, charges made before the run, raised size limits and an
//! expired deadline; the cancellation check injects a cancellation at each
//! charge point of the run in turn. Every run reserves a temporary first,
//! and after every run the inputs keep their stored forms,
//! `Context::retained()` is what it was before the run and a result is
//! canonical. Outcomes are compared by the stored form of the result, and
//! errors by their kind and the identifier of the exceeded limit, never by
//! message.
//!
//! The clock and the cancellation probe of these runs are written here: a
//! clock with a fixed reading, so that no run depends on the time, and a
//! probe that counts its polls and reports cancellation after a given
//! number.

use std::convert::Infallible;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use kalyx::coefficient::{CoefficientRing, ZeroTest};
use kalyx::context::{CancelProbe, Clock, Storage};
use kalyx::number::Integer;
use kalyx::polynomial::{Polynomial, PolynomialRing};
use kalyx::{Context, ErrorKind, LimitField, LimitId, Limits, Result};

use super::{Element, FieldLayer, Inspect, Lazy, Library, Polynomials, RingLayer, roomy};
use crate::support::case;

/// The work budget of the run that measures an operation, far above the
/// work of every operation that the checks measure. A measuring run that
/// exhausts it fails the check, so a regression that stops terminating
/// cannot hang it.
pub const MEASURE_WORK: u64 = 1_000_000;

/// The work checks try every budget up to the measured work when it is at
/// most this large, and a fixed selection of budgets otherwise.
pub const FULL_SWEEP: u64 = 400;

/// The work charged before the operation in the checks that charges are
/// kept.
pub const EARLIER_WORK: u64 = 5;

/// The temporary that every run reserves before it starts.
const RESERVED: Storage = Storage::new(1, 8);

/// The reading of the fixed clock, and the deadline that has passed at it.
const READING: u64 = 1_000;

/// A clock whose reading never changes.
#[derive(Clone, Copy, Debug)]
pub struct FixedClock(pub u64);

impl Clock for FixedClock {
    fn now(&mut self) -> u64 {
        self.0
    }

    fn fork(&self) -> Box<dyn Clock> {
        Box::new(*self)
    }
}

/// A probe that counts its polls and reports cancellation from the poll
/// after the first `cancel_after` polls on, as a flag set between two polls
/// does.
#[derive(Clone, Debug)]
pub struct CountingProbe {
    polls: Arc<AtomicU64>,
    cancel_after: u64,
}

impl CountingProbe {
    pub fn after(cancel_after: u64) -> Self {
        Self {
            polls: Arc::new(AtomicU64::new(0)),
            cancel_after,
        }
    }

    pub fn never() -> Self {
        Self::after(u64::MAX)
    }

    pub fn polls(&self) -> u64 {
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

/// A context with `limits`, the fixed clock and `probe`.
fn observed(limits: Limits, probe: &CountingProbe) -> Context {
    Context::with_observers(
        limits,
        Box::new(FixedClock(READING)),
        Box::new(probe.clone()),
    )
}

/// A context with `limits` and the work budget `budget`, which is never
/// cancelled.
fn with_budget(limits: &Limits, budget: u64) -> Context {
    observed(limits.with_max_work(budget), &CountingProbe::never())
}

/// The budgets that a work check tries for an operation that charges
/// `work`.
pub fn budgets(work: u64) -> Vec<u64> {
    if work <= FULL_SWEEP {
        return (0..=work + 1).collect();
    }
    let step = work / 128;
    let mut result: Vec<u64> = (0..=64).collect();
    result.extend((1..128).map(|i| i * step));
    result.extend(work - 64..=work + 1);
    result.push(work * 2);
    result.sort_unstable();
    result.dedup();
    result
}

/// `limits` with the measuring budget and each of the eight other fields
/// doubled.
pub fn raised(limits: &Limits) -> Limits {
    limits
        .with_max_work(MEASURE_WORK)
        .with_max_input_bytes(limits.max_input_bytes.saturating_mul(2))
        .with_max_output_bytes(limits.max_output_bytes.saturating_mul(2))
        .with_max_depth(limits.max_depth.saturating_mul(2))
        .with_max_nodes(limits.max_nodes.saturating_mul(2))
        .with_max_storage_bytes(limits.max_storage_bytes.saturating_mul(2))
        .with_max_integer_bits(limits.max_integer_bits.saturating_mul(2))
        .with_max_exponent(limits.max_exponent.saturating_mul(2))
        .with_max_frames(limits.max_frames.saturating_mul(2))
}

/// One operation under the checks: its label, its run on a context, the
/// stored form of its result, whether its result is canonical, and the
/// stored forms of its inputs.
pub struct Run<'a, T> {
    pub label: &'a str,
    pub run: &'a dyn Fn(&mut Context) -> Result<T>,
    pub show: &'a dyn Fn(&T) -> String,
    pub canonical: &'a dyn Fn(&T) -> bool,
    pub inputs: &'a dyn Fn() -> String,
}

/// The outcome of a run: the stored form of its result, or the kind of its
/// error with the identifier of the exceeded limit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    Value(String),
    Error(ErrorKind, Option<LimitId>),
}

impl Outcome {
    fn is_work_limit(&self) -> bool {
        *self
            == Self::Error(
                ErrorKind::ResourceLimit,
                Some(LimitId::Field(LimitField::Work)),
            )
    }

    fn kind(&self) -> Option<ErrorKind> {
        match self {
            Self::Value(_) => None,
            Self::Error(kind, _) => Some(*kind),
        }
    }
}

impl<T> Run<'_, T> {
    /// Runs on `context` with a reserved temporary, and checks that the
    /// inputs keep their stored forms, that the run leaves
    /// `Context::retained()` as it found it and that a result is canonical.
    fn on(&self, context: &mut Context) -> Outcome {
        let inputs = (self.inputs)();
        let reserved = context.reserve(RESERVED).unwrap();
        let before = context.retained();
        let result = (self.run)(context);
        assert_eq!(context.retained(), before, "{}: retained", self.label);
        context.release(reserved);
        assert_eq!((self.inputs)(), inputs, "{}: inputs changed", self.label);
        match result {
            Ok(value) => {
                assert!(
                    (self.canonical)(&value),
                    "{}: the noncanonical {}",
                    self.label,
                    (self.show)(&value)
                );
                Outcome::Value((self.show)(&value))
            }
            Err(error) => Outcome::Error(error.kind(), error.exceeded().map(|e| e.id().clone())),
        }
    }

    /// The measuring run: its outcome and its work.
    fn measure(&self, limits: &Limits, probe: &CountingProbe) -> (Outcome, u64) {
        let mut context = observed(limits.with_max_work(MEASURE_WORK), probe);
        let outcome = self.on(&mut context);
        assert!(
            !outcome.is_work_limit(),
            "{}: the measuring run exhausted {MEASURE_WORK} work units",
            self.label
        );
        (outcome, context.work_used())
    }
}

/// Checks the work accounting of `run` under `limits`.
///
/// For every tried budget $b$: the work never exceeds $b$; from $w$ on, the
/// run repeats the outcome and the work of the measuring run; below $w$ it
/// fails with `ResourceLimit` for `max_work`, and the work at the failure
/// does not decrease as $b$ grows. A run with exactly the work of a failure
/// as its budget stops with the same work, and with `EARLIER_WORK` charged
/// before it keeps those units as well; with `EARLIER_WORK` charged before a
/// budget of $w$ more, it repeats the outcome. Doubled size limits do not
/// change a run that no limit stopped. Under a deadline that has passed, a
/// run that charges fails at its first charge with `DeadlineExceeded` and no
/// work, and a run that charges nothing repeats its outcome.
pub fn work_accounting<T>(limits: &Limits, run: &Run<'_, T>) {
    let (expected, work) = run.measure(limits, &CountingProbe::never());
    case(
        Lazy(|f| write!(f, "work accounting of {}, work {work}", run.label)),
        || {
            if expected.kind() != Some(ErrorKind::ResourceLimit) {
                let mut context = observed(raised(limits), &CountingProbe::never());
                assert_eq!(run.on(&mut context), expected, "raised size limits");
                assert_eq!(context.work_used(), work, "work under raised size limits");
            }
            let mut stops: Vec<u64> = Vec::new();
            for budget in budgets(work) {
                let mut context = with_budget(limits, budget);
                let outcome = run.on(&mut context);
                let used = context.work_used();
                assert!(used <= budget, "work {used} above the budget {budget}");
                if budget >= work {
                    assert_eq!(outcome, expected, "budget {budget}");
                    assert_eq!(used, work, "work with budget {budget}");
                } else {
                    assert!(outcome.is_work_limit(), "budget {budget}: {outcome:?}");
                    assert!(
                        stops.last().is_none_or(|&last| last <= used),
                        "the work at a failure decreased with budget {budget}"
                    );
                    stops.push(used);
                }
            }
            stops.dedup();
            for used in stops {
                let mut context = with_budget(limits, used);
                assert!(run.on(&mut context).is_work_limit(), "stop at {used}");
                assert_eq!(context.work_used(), used, "the charges before a stop");
                let mut context = with_budget(limits, EARLIER_WORK + used);
                context.charge(EARLIER_WORK).unwrap();
                assert!(
                    run.on(&mut context).is_work_limit(),
                    "stop after earlier work"
                );
                assert_eq!(
                    context.work_used(),
                    EARLIER_WORK + used,
                    "earlier work kept"
                );
            }
            let mut context = with_budget(limits, EARLIER_WORK + work);
            context.charge(EARLIER_WORK).unwrap();
            assert_eq!(run.on(&mut context), expected, "after earlier work");
            assert_eq!(context.work_used(), EARLIER_WORK + work);
            let mut context = observed(limits.with_max_work(MEASURE_WORK), &CountingProbe::never())
                .with_deadline(READING);
            let outcome = run.on(&mut context);
            if work == 0 {
                // Only a run that charges nothing misses the deadline; it
                // repeats its outcome, including an error raised before any
                // charge.
                assert_eq!(outcome, expected, "a deadline and no charge");
            } else {
                assert_eq!(outcome.kind(), Some(ErrorKind::DeadlineExceeded));
                assert_eq!(context.work_used(), 0, "a passed deadline charges nothing");
            }
        },
    );
}

/// Checks the cancellation of `run` under `limits`: with $K$ the polls of a
/// probe that never cancels, a cancellation injected after $k - 1$ polls,
/// for each $k$ from 1 to $K$, stops the run at its $k$-th charge point with
/// `Cancelled`, and the probe is polled exactly $k$ times. A run that polls
/// no probe repeats its outcome under a probe that cancels at once.
pub fn cancellation<T>(limits: &Limits, run: &Run<'_, T>) {
    let probe = CountingProbe::never();
    let (expected, work) = run.measure(limits, &probe);
    let polls = probe.polls();
    case(
        Lazy(|f| {
            write!(
                f,
                "cancellation of {}, {polls} polls, work {work}",
                run.label
            )
        }),
        || {
            if polls == 0 {
                let probe = CountingProbe::after(0);
                let mut context = observed(limits.with_max_work(MEASURE_WORK), &probe);
                assert_eq!(run.on(&mut context), expected, "no charge point");
                assert_eq!(context.work_used(), 0);
            }
            for k in 1..=polls {
                let probe = CountingProbe::after(k - 1);
                let mut context = observed(limits.with_max_work(MEASURE_WORK), &probe);
                let outcome = run.on(&mut context);
                assert_eq!(
                    outcome.kind(),
                    Some(ErrorKind::Cancelled),
                    "charge point {k}"
                );
                assert_eq!(
                    probe.polls(),
                    k,
                    "polls of a run cancelled at charge point {k}"
                );
                assert!(context.work_used() <= work, "work of a cancelled run");
            }
        },
    );
}

/// Which check runs on each operation.
#[derive(Clone, Copy, Debug)]
pub enum Check {
    /// [`work_accounting`].
    Work,
    /// [`cancellation`].
    Cancellation,
}

impl Check {
    fn apply<T>(self, limits: &Limits, run: &Run<'_, T>) {
        match self {
            Self::Work => work_accounting(limits, run),
            Self::Cancellation => cancellation(limits, run),
        }
    }
}

/// The text of a zero test.
fn decision<U>(answer: &ZeroTest<U>) -> String {
    match answer {
        ZeroTest::Zero => "zero".into(),
        ZeroTest::Nonzero => "nonzero".into(),
        ZeroTest::Undecided(_) => "undecided".into(),
    }
}

/// A zero test is always canonical: it has no stored form to check.
fn decided<U>(_: &ZeroTest<U>) -> bool {
    true
}

/// Applies `check` to every element operation of a field: zero, one, the
/// images of $-7$, $0$ and $12$, and for each pair $(a, b)$ the zero test
/// of $a$, $a + b$, $a - b$, $a b$, $a / b$, $-a$ and $b^{-1}$, a zero
/// divisor included. Returns the number of runs.
pub fn element_accounting<A: Inspect>(
    check: Check,
    adapter: &A,
    limits: &Limits,
    pairs: &[(Element<A>, Element<A>)],
) -> usize
where
    A::Ring: FieldLayer,
{
    let ring = adapter.ring();
    let label = adapter.label();
    let show = |a: &Element<A>| adapter.representation(a);
    let canonical = |a: &Element<A>| adapter.canonical(a);
    let mut runs = 0;
    let mut apply = |what: String,
                     run: &dyn Fn(&mut Context) -> Result<Element<A>>,
                     inputs: &dyn Fn() -> String| {
        let label = format!("{label}: {what}");
        check.apply(
            limits,
            &Run {
                label: &label,
                run,
                show: &show,
                canonical: &canonical,
                inputs,
            },
        );
        runs += 1;
    };
    let none = String::new;
    apply("0".into(), &|c| ring.zero(c), &none);
    apply("1".into(), &|c| ring.one(c), &none);
    for n in [-7_i64, 0, 12] {
        let n = Integer::from(n);
        let inputs = || n.to_string();
        apply(format!("{n} * 1"), &|c| ring.from_integer(&n, c), &inputs);
    }
    for (a, b) in pairs {
        let (x, y) = (adapter.representation(a), adapter.representation(b));
        let inputs = || {
            format!(
                "{} {}",
                adapter.representation(a),
                adapter.representation(b)
            )
        };
        apply(format!("{x} + {y}"), &|c| ring.add(a, b, c), &inputs);
        apply(format!("{x} - {y}"), &|c| ring.subtract(a, b, c), &inputs);
        apply(format!("{x} * {y}"), &|c| ring.multiply(a, b, c), &inputs);
        apply(format!("{x} / {y}"), &|c| ring.divide(a, b, c), &inputs);
        apply(format!("-{x}"), &|c| ring.negate(a, c), &inputs);
        apply(format!("1 / {y}"), &|c| ring.inverse(b, c), &inputs);
    }
    for (a, b) in pairs {
        let inputs = || {
            format!(
                "{} {}",
                adapter.representation(a),
                adapter.representation(b)
            )
        };
        let label = format!("{label}: zero test of {}", adapter.representation(a));
        check.apply(
            limits,
            &Run {
                label: &label,
                run: &|c: &mut Context| ring.zero_test(a, c),
                show: &decision,
                canonical: &decided,
                inputs: &inputs,
            },
        );
        runs += 1;
    }
    runs
}

/// Applies `check` to every polynomial operation over a coefficient ring:
/// zero, one, the generator and the constant `factor`, and for each pair
/// $(a, b)$ $a + b$, $a - b$, $a b$, $a^3$, $a'$ and $-a$. Returns the
/// number of runs.
pub fn polynomial_accounting<K, A>(
    check: Check,
    ring: &PolynomialRing<K>,
    adapter: &A,
    limits: &Limits,
    factor: &K::Element,
    pairs: &[(Polynomial<K>, Polynomial<K>)],
) -> usize
where
    K: CoefficientRing<Undecided = Infallible>,
    A: Inspect<Ring = Library<K>>,
{
    let view = Polynomials { ring, adapter };
    let label = format!("polynomials over {}", adapter.label());
    let show = |p: &Polynomial<K>| view.representation(p);
    let canonical = |p: &Polynomial<K>| view.canonical(p, &mut roomy());
    let mut runs = 0;
    let mut apply = |what: String,
                     run: &dyn Fn(&mut Context) -> Result<Polynomial<K>>,
                     inputs: &dyn Fn() -> String| {
        let label = format!("{label}: {what}");
        check.apply(
            limits,
            &Run {
                label: &label,
                run,
                show: &show,
                canonical: &canonical,
                inputs,
            },
        );
        runs += 1;
    };
    let none = String::new;
    apply("0".into(), &|c| ring.zero(c), &none);
    apply("1".into(), &|c| ring.one(c), &none);
    apply("x".into(), &|c| ring.generator(c), &none);
    let constant = || adapter.representation(factor);
    apply("constant".into(), &|c| ring.constant(factor, c), &constant);
    for (a, b) in pairs {
        let (x, y) = (view.representation(a), view.representation(b));
        let inputs = || format!("{} {}", view.representation(a), view.representation(b));
        apply(format!("{x} + {y}"), &|c| ring.add(a, b, c), &inputs);
        apply(format!("{x} - {y}"), &|c| ring.subtract(a, b, c), &inputs);
        apply(format!("{x} * {y}"), &|c| ring.multiply(a, b, c), &inputs);
        apply(format!("({x})^3"), &|c| ring.power(a, 3, c), &inputs);
        apply(format!("({x})'"), &|c| ring.derivative(a, c), &inputs);
        apply(format!("-({x})"), &|c| ring.negate(a, c), &inputs);
    }
    runs
}
