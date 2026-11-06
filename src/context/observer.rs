//! The readings of the world outside a computation: the injected clock and
//! the injected cancellation probe, with their default implementations.
//!
//! This module is the adapter of the context. The charging core reads the
//! clock and the probe only through the crate-internal `Observer`, which holds
//! them; the atomic flag of [`CancelFlag`] is the only shared state, and it
//! lives here.

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;

/// A monotonic clock, read by the context at fixed charge points.
///
/// [`now`](Clock::now) returns nanoseconds from an origin of the clock's own
/// choosing; readings never decrease. Tests inject a fake clock; the default
/// is [`MonotonicClock`].
pub trait Clock: Send {
    /// The current reading, in nanoseconds.
    fn now(&mut self) -> u64;

    /// A clock with the same origin. The context of this release does not
    /// call it; it is kept so that sub-budgets of a later release need no
    /// change of the trait.
    fn fork(&self) -> Box<dyn Clock>;
}

/// A cancellation probe, polled by the context first at every charge.
///
/// Once it answers `true` it keeps answering `true`. Tests inject a fake
/// probe; the default is [`CancelFlag`].
pub trait CancelProbe: Send {
    /// Whether the request has been cancelled.
    fn is_cancelled(&mut self) -> bool;

    /// A probe that observes the same signal. The context of this release
    /// does not call it; it is kept for the same reason as [`Clock::fork`].
    fn fork(&self) -> Box<dyn CancelProbe>;
}

/// The default clock: [`std::time::Instant`], measured from the creation of
/// the clock.
#[derive(Clone, Copy, Debug)]
pub struct MonotonicClock {
    origin: Instant,
}

impl MonotonicClock {
    /// A clock whose origin is now.
    #[must_use]
    pub fn new() -> Self {
        Self {
            origin: Instant::now(),
        }
    }
}

impl Default for MonotonicClock {
    /// A clock whose origin is now, the same as [`MonotonicClock::new`].
    fn default() -> Self {
        Self::new()
    }
}

impl Clock for MonotonicClock {
    /// The nanoseconds since the origin, or `u64::MAX` after about 584 years.
    fn now(&mut self) -> u64 {
        u64::try_from(self.origin.elapsed().as_nanos()).unwrap_or(u64::MAX)
    }

    fn fork(&self) -> Box<dyn Clock> {
        Box::new(*self)
    }
}

/// The default cancellation probe: a one-way flag that its clones share.
///
/// Cancelling any clone cancels them all, from any thread. A flag set by
/// another thread becomes visible eventually, and the context observes it at
/// the next charge point after that.
///
/// ```
/// use kalyx::context::CancelFlag;
///
/// let flag = CancelFlag::new();
/// let shared = flag.clone();
/// shared.cancel();
/// assert!(flag.is_cancelled());
/// assert!(!CancelFlag::new().is_cancelled());
/// ```
#[derive(Clone, Debug, Default)]
pub struct CancelFlag(Arc<AtomicBool>);

impl CancelFlag {
    /// A new flag, not cancelled and shared with no other flag.
    #[must_use]
    pub fn new() -> Self {
        Self(Arc::new(AtomicBool::new(false)))
    }

    /// Cancels the flag and all its clones.
    pub fn cancel(&self) {
        self.0.store(true, Ordering::Relaxed);
    }

    /// Whether the flag has been cancelled.
    #[must_use]
    pub fn is_cancelled(&self) -> bool {
        self.0.load(Ordering::Relaxed)
    }
}

impl CancelProbe for CancelFlag {
    fn is_cancelled(&mut self) -> bool {
        self.0.load(Ordering::Relaxed)
    }

    fn fork(&self) -> Box<dyn CancelProbe> {
        Box::new(self.clone())
    }
}

/// The clock and the probe of a context, opaque to the charging core. Every
/// reading takes `&mut self` and makes one reading per call.
pub(crate) struct Observer {
    clock: Box<dyn Clock>,
    probe: Box<dyn CancelProbe>,
}

impl Observer {
    pub(crate) fn new(clock: Box<dyn Clock>, probe: Box<dyn CancelProbe>) -> Self {
        Self { clock, probe }
    }

    /// Whether the probe reports cancellation.
    pub(crate) fn cancelled(&mut self) -> bool {
        self.probe.is_cancelled()
    }

    /// Whether the clock has reached `deadline`.
    pub(crate) fn reached(&mut self, deadline: u64) -> bool {
        self.clock.now() >= deadline
    }

    /// One reading of the clock.
    pub(crate) fn now(&mut self) -> u64 {
        self.clock.now()
    }
}
