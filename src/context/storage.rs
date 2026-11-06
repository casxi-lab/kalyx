//! Logical storage costs: the retained nodes and bytes of a value.

/// The logical storage cost of a retained value, a frame or a temporary: its
/// nodes and its logical bytes.
///
/// The bytes are computed from bit lengths by the formula of the value kind;
/// they are not the memory that the value occupies. The context receives
/// computed costs and never computes a formula.
///
/// ```
/// use kalyx::context::Storage;
///
/// let cost = Storage::new(3, 11);
/// assert_eq!((cost.nodes, cost.bytes), (3, 11));
/// assert_eq!(cost.saturating_add(Storage::new(u64::MAX, 1)), Storage::new(u64::MAX, 12));
/// ```
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct Storage {
    /// The retained nodes.
    pub nodes: u64,
    /// The retained logical bytes.
    pub bytes: u64,
}

impl Storage {
    /// The cost of nothing.
    pub const ZERO: Self = Self { nodes: 0, bytes: 0 };

    /// The cost of `nodes` nodes and `bytes` logical bytes.
    #[must_use]
    pub const fn new(nodes: u64, bytes: u64) -> Self {
        Self { nodes, bytes }
    }

    /// The sum of each component, stopping at `u64::MAX`.
    ///
    /// For the formulas of value kinds and for reported amounts. The retained
    /// totals of the context are exact sums, and a sum there that does not fit
    /// in a `u64` exceeds the limit.
    #[must_use]
    pub const fn saturating_add(self, other: Self) -> Self {
        Self {
            nodes: self.nodes.saturating_add(other.nodes),
            bytes: self.bytes.saturating_add(other.bytes),
        }
    }

    /// The difference of each component, stopping at zero.
    #[must_use]
    pub const fn saturating_sub(self, other: Self) -> Self {
        Self {
            nodes: self.nodes.saturating_sub(other.nodes),
            bytes: self.bytes.saturating_sub(other.bytes),
        }
    }
}

/// A value kind whose values have a logical storage cost.
///
/// Each value kind has one formula, which depends only on the value, never on
/// the platform or the memory layout, and which its component's contract
/// states. The context takes the [`Storage`] that the formula gives; it never
/// calls this trait.
pub trait StorageCost {
    /// The cost of this value.
    fn storage(&self) -> Storage;
}
