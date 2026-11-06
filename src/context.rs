//! The request context: limits, deterministic charging, the deadline and
//! cancellation, bounded output, and the accounting of frames and temporaries.
//!
//! One [`Context`] accounts for one request. Every stage of the request
//! charges it, in a fixed order, so the same request under the same limits
//! charges the same work and reaches the same result. Each charge polls the
//! injected [`CancelProbe`] first, then reads the injected [`Clock`] at fixed
//! points to observe the deadline, then checks the work limit; the checks are
//! cooperative, so a running primitive operation is never interrupted.
//!
//! The rules of this module are stated in the component contract,
//! `docs/components/context/contract.md`.
//!
//! ```
//! use kalyx::context::CancelFlag;
//! use kalyx::{Context, ErrorKind, LimitField, Limits};
//!
//! let flag = CancelFlag::new();
//! let mut context = Context::new(Limits::new().with_max_work(10), flag.clone());
//! context.charge(4)?;
//! context.charge(6)?;
//! assert_eq!(context.work_used(), 10);
//!
//! let exhausted = context.charge(1).unwrap_err();
//! assert_eq!(exhausted.kind(), ErrorKind::ResourceLimit);
//! let limit = exhausted.exceeded().expect("a resource limit names its limit");
//! assert_eq!(limit.id().name(), LimitField::Work.name());
//!
//! flag.cancel();
//! assert_eq!(context.charge(0).unwrap_err().kind(), ErrorKind::Cancelled);
//! # Ok::<(), kalyx::Error>(())
//! ```

mod limits;
mod observer;
mod storage;
#[cfg(test)]
mod tests;

use std::fmt;

pub use limits::Limits;
pub use observer::{CancelFlag, CancelProbe, Clock, MonotonicClock};
pub use storage::{Storage, StorageCost};

use crate::{Error, LimitAmount, LimitExceeded, LimitField, LimitId, LimitScope, Result, Span};
use observer::Observer;

/// While a deadline is set and no expiry has been observed, at most
/// `POLL_WINDOW - 1` consecutive small charges read no clock.
pub const POLL_WINDOW: u32 = 64;

/// A charge of at least this many units is large: it reads the clock before
/// the work it pays for, and the next charge reads the clock as well.
pub const LARGE_CHARGE: u64 = 64;

/// The largest overrun of a small reading: the charge that read the clock and
/// the `POLL_WINDOW - 1` small charges after it, each below `LARGE_CHARGE`.
const SMALL_OVERRUN: u64 = (POLL_WINDOW as u64) * (LARGE_CHARGE - 1);

/// The bound, in work units, on the work charged after a deadline passes
/// and before a charge fails with `DeadlineExceeded`: $\max(4032, L)$, where
/// `last_large` is the amount $L$ of the last large charge that read the clock
/// before the deadline, or 0 when there was none. One primitive operation
/// that is running when the deadline passes comes on top of it.
///
/// A small or zero charge that reads the clock is followed by at most 63 small
/// charges without a reading, each of at most 63 units, so its own work and
/// theirs are at most $64 \cdot 63 = 4032$ units. A large charge reads the
/// clock before its work, and the next charge reads it again, so the work
/// after its reading is its own amount.
///
/// ```
/// use kalyx::context::overrun_bound;
///
/// assert_eq!(overrun_bound(0), 4032);
/// assert_eq!(overrun_bound(64), 4032);
/// assert_eq!(overrun_bound(50_000), 50_000);
/// ```
#[must_use]
pub const fn overrun_bound(last_large: u64) -> u64 {
    if last_large > SMALL_OVERRUN {
        last_large
    } else {
        SMALL_OVERRUN
    }
}

/// An open frame, returned by [`Context::enter_frame`].
///
/// The token records the position of its frame and the generation number of
/// the frame, so a token whose frame was closed never reaches a frame that
/// was opened later in its place. It cannot be cloned: each frame has one
/// token, which [`Context::leave_frame`] takes back.
#[derive(Debug)]
#[must_use = "a frame stays open until it is passed to `Context::leave_frame`"]
pub struct Frame {
    index: usize,
    generation: u64,
}

/// A reserved temporary, returned by [`Context::reserve`] and retained until
/// [`Context::release`] takes it back. It cannot be cloned.
#[derive(Debug)]
#[must_use = "a reservation is retained until it is passed to `Context::release`"]
pub struct Reserved {
    cost: Storage,
}

impl Reserved {
    /// The cost that the reservation retains.
    #[must_use]
    pub const fn cost(&self) -> Storage {
        self.cost
    }
}

/// One entry of the frame table: the cost of an open frame and the generation
/// number it was entered with.
#[derive(Clone, Copy, Debug)]
struct FrameEntry {
    cost: Storage,
    generation: u64,
}

/// The cooperative accounting of one request.
///
/// A context holds the [`Limits`] of the request, the work and the output
/// charged so far, the deadline, the injected clock and cancellation probe,
/// and the frame table with the reserved temporaries. It holds no settings
/// and no progress receiver: those are inputs of the request and parameters
/// of its entry. Only the command entry and the command-line program create a
/// context; library code charges the context that it was given, and a
/// sub-computation charges the same context as its caller.
///
/// A context cannot be cloned, so its accounting is never shared by two
/// copies.
pub struct Context {
    limits: Limits,
    // Invariant: work <= limits.max_work.
    work: u64,
    // Invariant: output <= limits.max_output_bytes.
    output: u64,
    // The deadline as a reading of the clock.
    deadline: Option<u64>,
    // The small charges that may pass before the clock is read again.
    // Invariant: credit < POLL_WINDOW.
    credit: u32,
    // An observed expiry, final until a deadline is set again.
    expired: bool,
    // One entry per open frame, innermost last; only a pointer is kept inline
    // until the first frame allocates the table, which then keeps its
    // capacity. Invariant: its length is at most limits.max_frames.
    #[allow(
        clippy::box_collection,
        reason = "one pointer inline until the first frame, as the frame table of the source"
    )]
    frames: Option<Box<Vec<FrameEntry>>>,
    // The frames entered so far: the generation number of the next frame.
    // Invariant: entered <= work, since every frame entered charged one unit.
    entered: u64,
    // Invariant: frames_total is the sum of the costs in the frame table, and
    // frames_total + temporaries is at most (max_nodes, max_storage_bytes)
    // in each component, so that sum never overflows.
    frames_total: Storage,
    // The sum of the reserved temporaries.
    temporaries: Storage,
    observer: Observer,
}

impl Context {
    /// A context with `limits`, the [`MonotonicClock`] and the cancellation
    /// flag `cancel`, and no deadline.
    #[must_use]
    pub fn new(limits: Limits, cancel: CancelFlag) -> Self {
        Self::with_observers(limits, Box::new(MonotonicClock::new()), Box::new(cancel))
    }

    /// A context with `limits`, the clock `clock` and the cancellation probe
    /// `probe`, and no deadline.
    #[must_use]
    pub fn with_observers(
        limits: Limits,
        clock: Box<dyn Clock>,
        probe: Box<dyn CancelProbe>,
    ) -> Self {
        Self {
            limits,
            work: 0,
            output: 0,
            deadline: None,
            credit: 0,
            expired: false,
            frames: None,
            entered: 0,
            frames_total: Storage::ZERO,
            temporaries: Storage::ZERO,
            observer: Observer::new(clock, probe),
        }
    }

    /// This context with the deadline `at`, a reading of its clock in
    /// nanoseconds, in place of any earlier deadline. The next charge that
    /// observes no cancellation reads the clock, whatever its amount, and an
    /// earlier observed expiry no longer counts.
    #[must_use]
    pub fn with_deadline(mut self, at: u64) -> Self {
        self.deadline = Some(at);
        self.credit = 0;
        self.expired = false;
        self
    }

    /// This context with a deadline `nanos` nanoseconds after one reading of
    /// its clock, taken now; a deadline beyond the range of the clock is
    /// `u64::MAX`.
    #[must_use]
    pub fn with_timeout(mut self, nanos: u64) -> Self {
        let now = self.observer.now();
        self.with_deadline(now.saturating_add(nanos))
    }

    /// The limits of the request.
    #[must_use]
    pub const fn limits(&self) -> &Limits {
        &self.limits
    }

    /// The work charged so far.
    #[must_use]
    pub const fn work_used(&self) -> u64 {
        self.work
    }

    /// The output bytes charged so far.
    #[must_use]
    pub const fn output_used(&self) -> u64 {
        self.output
    }

    /// The number of open frames.
    #[must_use]
    pub fn open_frames(&self) -> u64 {
        self.frame_count() as u64
    }

    /// The cost recorded for `frame`, or `None` when the frame is no longer
    /// open.
    #[must_use]
    pub fn frame_cost(&self, frame: &Frame) -> Option<Storage> {
        match &self.frames {
            Some(frames) => {
                if frame.index < frames.len() && frames[frame.index].generation == frame.generation
                {
                    Some(frames[frame.index].cost)
                } else {
                    None
                }
            }
            None => None,
        }
    }

    /// Everything retained: the costs of the open frames plus the reserved
    /// temporaries.
    #[must_use]
    pub const fn retained(&self) -> Storage {
        // Exact: the sum is within the limits by the invariant.
        self.frames_total.saturating_add(self.temporaries)
    }

    /// Charges `units` of work.
    ///
    /// Polls cancellation first, then the deadline, then checks `max_work`,
    /// and adds the units only when all three pass; a failed charge changes
    /// nothing but the polling state. A zero charge reads the clock without
    /// consuming work. The amount depends only on the operation that it pays
    /// for, never on the limits or on the remaining work.
    ///
    /// # Errors
    ///
    /// `Cancelled` when the probe reports cancellation, `DeadlineExceeded`
    /// when the deadline has been observed to pass, and `ResourceLimit` with
    /// `LimitField::Work` when the work would exceed `max_work`.
    pub fn charge(&mut self, units: u64) -> Result<()> {
        self.charge_at(units, None)
    }

    /// [`charge`](Context::charge), with `span` on the error.
    pub(crate) fn charge_at(&mut self, units: u64, span: Option<Span>) -> Result<()> {
        self.observe(units, span)?;
        let work = self.admit_work(units, span)?;
        self.work = work;
        Ok(())
    }

    /// Charges `bytes` of output: polls as a charge of `bytes` units, checks
    /// the request's cumulative `max_output_bytes`, then charges one work unit
    /// per byte. A caller writes the bytes only after every charge for them
    /// has succeeded, so a failure leaves no partial output.
    ///
    /// # Errors
    ///
    /// As [`charge`](Context::charge), and `ResourceLimit` with
    /// `LimitField::OutputBytes` when the output would exceed
    /// `max_output_bytes`.
    pub fn charge_output(&mut self, bytes: u64) -> Result<()> {
        self.observe(bytes, None)?;
        let output = self.admit_output(bytes)?;
        let work = self.admit_work(bytes, None)?;
        self.work = work;
        self.output = output;
        Ok(())
    }

    /// Polls cancellation, then the deadline for a charge of `amount`.
    fn observe(&mut self, amount: u64, span: Option<Span>) -> Result<()> {
        if self.observer.cancelled() {
            return Err(Error::cancelled(span));
        }
        if self.poll_deadline(amount) {
            return Err(Error::deadline_exceeded(span));
        }
        Ok(())
    }

    /// Whether an expiry is observed at a charge of `amount`. The clock is
    /// read for a zero charge, for a large charge and when the credit of small
    /// charges is spent; a large charge leaves no credit, so the charge after
    /// it reads the clock as well.
    fn poll_deadline(&mut self, amount: u64) -> bool {
        let deadline = match self.deadline {
            Some(deadline) => deadline,
            None => return false,
        };
        if self.expired {
            return true;
        }
        if amount == 0 || amount >= LARGE_CHARGE || self.credit == 0 {
            self.credit = if amount >= LARGE_CHARGE {
                0
            } else {
                POLL_WINDOW - 1
            };
            self.expired = self.observer.reached(deadline);
            self.expired
        } else {
            // The credit is positive here.
            self.credit -= 1;
            false
        }
    }

    /// The work after `amount` more; writes nothing.
    fn admit_work(&mut self, amount: u64, span: Option<Span>) -> Result<u64> {
        let total = match self.work.checked_add(amount) {
            Some(total) => total,
            None => return Err(self.exhausted(LimitAmount::Bound(u64::MAX), span)),
        };
        if total > self.limits.max_work {
            return Err(self.exhausted(LimitAmount::Required(total), span));
        }
        Ok(total)
    }

    /// The error of exhausted work. With a deadline set, the clock is read
    /// once more first, and an expiry takes precedence.
    fn exhausted(&mut self, amount: LimitAmount, span: Option<Span>) -> Error {
        if self.deadline_reached() {
            self.expired = true;
            return Error::deadline_exceeded(span);
        }
        field_exceeded(LimitField::Work, self.limits.max_work, amount, span)
    }

    /// One reading of the clock against the deadline; false without one.
    fn deadline_reached(&mut self) -> bool {
        match self.deadline {
            Some(deadline) => self.observer.reached(deadline),
            None => false,
        }
    }

    /// The output after `bytes` more; writes nothing.
    fn admit_output(&self, bytes: u64) -> Result<u64> {
        let allowed = self.limits.max_output_bytes;
        let total = match self.output.checked_add(bytes) {
            Some(total) => total,
            None => {
                return Err(field_exceeded(
                    LimitField::OutputBytes,
                    allowed,
                    LimitAmount::Bound(u64::MAX),
                    None,
                ));
            }
        };
        if total > allowed {
            return Err(field_exceeded(
                LimitField::OutputBytes,
                allowed,
                LimitAmount::Required(total),
                None,
            ));
        }
        Ok(total)
    }

    /// Checks `value` against the field `field`; charges, reads and changes
    /// nothing.
    ///
    /// For `Nodes` this is `check_storage(Storage::new(value, 0),
    /// LimitScope::Value)` and for `StorageBytes` it is
    /// `check_storage(Storage::new(0, value), LimitScope::Value)`, so the
    /// open frames and the reserved temporaries count as well, and the error
    /// has the scope `Value`. Every other field compares the single value,
    /// and the error has no scope.
    ///
    /// # Errors
    ///
    /// `ResourceLimit` with `LimitField` `field` when `value` exceeds it.
    pub fn check(&self, field: LimitField, value: u64) -> Result<()> {
        self.check_at(field, value, None)
    }

    /// [`check`](Context::check), with `span` on the error.
    pub(crate) fn check_at(&self, field: LimitField, value: u64, span: Option<Span>) -> Result<()> {
        match field {
            LimitField::Nodes => {
                self.check_storage_at(Storage::new(value, 0), LimitScope::Value, span)
            }
            LimitField::StorageBytes => {
                self.check_storage_at(Storage::new(0, value), LimitScope::Value, span)
            }
            LimitField::Work
            | LimitField::InputBytes
            | LimitField::OutputBytes
            | LimitField::Depth
            | LimitField::IntegerBits
            | LimitField::Exponent
            | LimitField::Frames => {
                let allowed = self.limits.get(field);
                if value > allowed {
                    return Err(field_exceeded(
                        field,
                        allowed,
                        LimitAmount::Required(value),
                        span,
                    ));
                }
                Ok(())
            }
        }
    }

    /// Checks `value` against the explicit request parameter `name`, whose
    /// value is `allowed`; charges, reads and changes nothing.
    ///
    /// # Errors
    ///
    /// `ResourceLimit` naming the parameter `name` when `value` exceeds
    /// `allowed`.
    pub fn check_parameter(&self, name: &str, allowed: u64, value: u64) -> Result<()> {
        if value > allowed {
            let exceeded = LimitExceeded::new(
                LimitId::Parameter(String::from(name)),
                None,
                allowed,
                LimitAmount::Required(value),
            );
            return Err(Error::resource_limit(exceeded, None));
        }
        Ok(())
    }

    /// Checks that a value of cost `cost` fits together with the open frames
    /// and the reserved temporaries, at `scope`; charges, reads and changes
    /// nothing, and takes constant time.
    ///
    /// # Errors
    ///
    /// `ResourceLimit` with `LimitField::Nodes`, or else
    /// `LimitField::StorageBytes`, and the scope `scope`, when the sum
    /// exceeds `max_nodes` or `max_storage_bytes`; a sum that does not fit in
    /// a `u64` exceeds the limit, with the amount `LimitAmount::Bound`.
    pub fn check_storage(&self, cost: Storage, scope: LimitScope) -> Result<()> {
        self.check_storage_at(cost, scope, None)
    }

    /// [`check_storage`](Context::check_storage), with `span` on the error.
    pub(crate) fn check_storage_at(
        &self,
        cost: Storage,
        scope: LimitScope,
        span: Option<Span>,
    ) -> Result<()> {
        self.admit(self.frames_total, cost, scope, span)?;
        Ok(())
    }

    /// The exact sum of `frames`, the temporaries and `cost`, checked against
    /// `max_nodes`, then `max_storage_bytes`, at `scope`; writes nothing.
    fn admit(
        &self,
        frames: Storage,
        cost: Storage,
        scope: LimitScope,
        span: Option<Span>,
    ) -> Result<Storage> {
        let nodes = match fit(
            frames.nodes,
            self.temporaries.nodes,
            cost.nodes,
            self.limits.max_nodes,
        ) {
            Fit::Within(nodes) => nodes,
            Fit::Over(amount) => {
                return Err(retained_exceeded(
                    Retained::Nodes,
                    self.limits.max_nodes,
                    amount,
                    scope,
                    span,
                ));
            }
        };
        let bytes = match fit(
            frames.bytes,
            self.temporaries.bytes,
            cost.bytes,
            self.limits.max_storage_bytes,
        ) {
            Fit::Within(bytes) => bytes,
            Fit::Over(amount) => {
                return Err(retained_exceeded(
                    Retained::StorageBytes,
                    self.limits.max_storage_bytes,
                    amount,
                    scope,
                    span,
                ));
            }
        };
        Ok(Storage::new(nodes, bytes))
    }

    /// Reserves a temporary of cost `cost` until the token is released.
    ///
    /// Checks the open frames, the reserved temporaries and `cost` together,
    /// at `LimitScope::Temporary`. A reservation charges no work, reads
    /// neither the clock nor the probe and is not a charge point. A zero
    /// reservation is not checked.
    ///
    /// # Errors
    ///
    /// As [`check_storage`](Context::check_storage) at
    /// `LimitScope::Temporary`; a failure changes nothing.
    pub fn reserve(&mut self, cost: Storage) -> Result<Reserved> {
        if cost == Storage::ZERO {
            return Ok(Reserved { cost });
        }
        let total = self.admit(self.frames_total, cost, LimitScope::Temporary, None)?;
        // Exact: the total includes the frame costs.
        self.temporaries = total.saturating_sub(self.frames_total);
        Ok(Reserved { cost })
    }

    /// Releases a reservation.
    pub fn release(&mut self, reserved: Reserved) {
        let Reserved { cost } = reserved;
        self.temporaries = self.temporaries.saturating_sub(cost);
    }

    /// Opens a frame of cost zero and charges one unit.
    ///
    /// Polls as a charge of one unit, then checks `max_work` and that fewer
    /// than `max_frames` frames are open, and only then charges and opens the
    /// frame: a rejected frame is not charged.
    ///
    /// # Errors
    ///
    /// As [`charge`](Context::charge), and `ResourceLimit` with
    /// `LimitField::Frames` when `max_frames` frames are open.
    pub fn enter_frame(&mut self) -> Result<Frame> {
        self.observe(1, None)?;
        let work = self.admit_work(1, None)?;
        let count = self.frame_count();
        let open = count as u64;
        if open >= self.limits.max_frames {
            return Err(field_exceeded(
                LimitField::Frames,
                self.limits.max_frames,
                LimitAmount::Required(open.saturating_add(1)),
                None,
            ));
        }
        let generation = self.entered;
        self.work = work;
        // Never saturates: entered is at most the work charged.
        self.entered = generation.saturating_add(1);
        self.push_frame(FrameEntry {
            cost: Storage::ZERO,
            generation,
        });
        Ok(Frame {
            index: count,
            generation,
        })
    }

    /// Appends `entry` to the frame table, allocating the table at the first
    /// frame.
    fn push_frame(&mut self, entry: FrameEntry) {
        match &mut self.frames {
            Some(frames) => frames.push(entry),
            None => {
                let mut frames = Box::new(Vec::new());
                frames.push(entry);
                self.frames = Some(frames);
            }
        }
    }

    /// Records `cost` as the cost of the open frame `frame`, in place of its
    /// earlier cost, and charges one unit.
    ///
    /// Polls as a charge of one unit, checks `max_work`, then checks the
    /// other open frames, the reserved temporaries and `cost` together at
    /// `LimitScope::Frame`, and only then charges and records the cost: a
    /// rejected cost is not charged and leaves the frame table unchanged. Any
    /// open frame may be given a cost, not only the innermost. A frame that is
    /// no longer open is charged one unit and records nothing.
    ///
    /// # Errors
    ///
    /// As [`charge`](Context::charge), and as
    /// [`check_storage`](Context::check_storage) at `LimitScope::Frame`.
    pub fn set_frame_cost(&mut self, frame: &Frame, cost: Storage) -> Result<()> {
        self.observe(1, None)?;
        let work = self.admit_work(1, None)?;
        let old = match self.frame_cost(frame) {
            Some(old) => old,
            None => {
                self.work = work;
                return Ok(());
            }
        };
        // Exact: the old cost is a part of frames_total.
        let others = self.frames_total.saturating_sub(old);
        let total = self.admit(others, cost, LimitScope::Frame, None)?;
        self.work = work;
        // The frame is open, so the write below takes place.
        self.write_frame_cost(frame.index, cost);
        // Exact: the total includes the temporaries.
        self.frames_total = total.saturating_sub(self.temporaries);
        Ok(())
    }

    /// Writes the cost of the frame at `index`, when that frame is open.
    #[expect(
        clippy::single_match,
        clippy::collapsible_match,
        reason = "the provable subset writes every match on an Option as a `match` \
                  and keeps the bounds check in the arm, not in a match guard"
    )]
    fn write_frame_cost(&mut self, index: usize, cost: Storage) {
        match &mut self.frames {
            Some(frames) => {
                if index < frames.len() {
                    frames[index].cost = cost;
                }
            }
            None => {}
        }
    }

    /// Closes `frame` and every frame opened after it, and subtracts their
    /// costs from the retained total. A frame that is no longer open closes
    /// nothing. Takes one step per frame closed, each of which was charged
    /// when it was entered.
    #[expect(
        clippy::collapsible_match,
        reason = "the provable subset keeps the check of the token in the arm, \
                  not in a match guard"
    )]
    pub fn leave_frame(&mut self, frame: Frame) {
        let Frame { index, generation } = frame;
        let rest = match &self.frames {
            Some(frames) => {
                if index < frames.len() && frames[index].generation == generation {
                    without_frames(frames, index, self.frames_total)
                } else {
                    return;
                }
            }
            None => return,
        };
        self.frames_total = rest;
        self.truncate_frames(index);
    }

    /// Closes the frames from `index` on.
    #[expect(
        clippy::single_match,
        reason = "the provable subset writes every match on an Option as a `match`"
    )]
    fn truncate_frames(&mut self, index: usize) {
        match &mut self.frames {
            Some(frames) => frames.truncate(index),
            None => {}
        }
    }

    /// The number of open frames.
    fn frame_count(&self) -> usize {
        match &self.frames {
            Some(frames) => frames.len(),
            None => 0,
        }
    }
}

impl fmt::Debug for Context {
    /// The limits and the state of the accounting; the clock and the probe
    /// are not shown.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Context")
            .field("limits", &self.limits)
            .field("work", &self.work)
            .field("output", &self.output)
            .field("deadline", &self.deadline)
            .field("expired", &self.expired)
            .field("frames", &self.frame_count())
            .field("frames_total", &self.frames_total)
            .field("temporaries", &self.temporaries)
            .finish_non_exhaustive()
    }
}

/// `total` less the costs of the frames from `from` on: one step per frame.
fn without_frames(frames: &[FrameEntry], from: usize, total: Storage) -> Storage {
    let mut rest = total;
    let mut index = from;
    while index < frames.len() {
        rest = rest.saturating_sub(frames[index].cost);
        index += 1;
    }
    rest
}

/// The result of checking one component of a retained total.
enum Fit {
    /// The exact sum, within the limit.
    Within(u64),
    /// The amount beyond the limit.
    Over(LimitAmount),
}

/// The exact sum `a + b + c`, checked against `allowed`. A sum that does not
/// fit in a `u64` exceeds every limit, with the amount `u64::MAX` as a bound.
fn fit(a: u64, b: u64, c: u64, allowed: u64) -> Fit {
    let partial = match a.checked_add(b) {
        Some(partial) => partial,
        None => return Fit::Over(LimitAmount::Bound(u64::MAX)),
    };
    let total = match partial.checked_add(c) {
        Some(total) => total,
        None => return Fit::Over(LimitAmount::Bound(u64::MAX)),
    };
    if total > allowed {
        return Fit::Over(LimitAmount::Required(total));
    }
    Fit::Within(total)
}

/// The two retained totals, the only fields reported with a scope.
#[derive(Clone, Copy)]
enum Retained {
    Nodes,
    StorageBytes,
}

/// The error of an exceeded retained total, with its scope. The scope of a
/// `LimitExceeded` is `Some` exactly for `Nodes` and `StorageBytes`: this is
/// the only place that builds one with a scope, and it takes a `Retained`.
fn retained_exceeded(
    measure: Retained,
    allowed: u64,
    amount: LimitAmount,
    scope: LimitScope,
    span: Option<Span>,
) -> Error {
    let field = match measure {
        Retained::Nodes => LimitField::Nodes,
        Retained::StorageBytes => LimitField::StorageBytes,
    };
    let exceeded = LimitExceeded::new(LimitId::Field(field), Some(scope), allowed, amount);
    Error::resource_limit(exceeded, span)
}

/// The error of an exceeded field without a scope. Its callers pass `Work`,
/// `OutputBytes` and `Frames`, and in [`Context::check`] the seven fields
/// other than `Nodes` and `StorageBytes`, which go through
/// [`retained_exceeded`] instead.
fn field_exceeded(
    field: LimitField,
    allowed: u64,
    amount: LimitAmount,
    span: Option<Span>,
) -> Error {
    let exceeded = LimitExceeded::new(LimitId::Field(field), None, allowed, amount);
    Error::resource_limit(exceeded, span)
}

// A context, a frame and a reservation cannot be cloned: each of these fails
// to compile once its type implements `Clone`, and so `Copy`, since the
// parameter `A` of `not_clone` can then be inferred in two ways.
mod clone_guard {
    pub(super) trait AmbiguousIfClone<A> {}
    impl<T: ?Sized> AmbiguousIfClone<()> for T {}
    impl<T: Clone> AmbiguousIfClone<u8> for T {}

    pub(super) const fn not_clone<T: ?Sized + AmbiguousIfClone<A>, A>() {}
}
const _: () = clone_guard::not_clone::<Context, _>();
const _: () = clone_guard::not_clone::<Frame, _>();
const _: () = clone_guard::not_clone::<Reserved, _>();
