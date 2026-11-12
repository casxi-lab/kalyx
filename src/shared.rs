//! The shared result types: the evidence of a decision, [`Evidence`], and a
//! three-valued truth value, [`Truth`].
//!
//! Each type is defined once for the whole crate, here, and reaches callers
//! only through the crate root, since this module is private. Both are
//! values of an answer, never request failures. Building and combining them
//! takes no context and charges nothing. The rules are stated in the
//! component contract, `docs/components/shared-results/contract.md`.

/// The evidence of a decision: whether a proposition is proved or refuted,
/// holds numerically without a proof, or is undecided.
///
/// `Proved` and `Refuted` decide the proposition. `NumericEvidence` is
/// evidence that it holds numerically, which is not a proof, and `Unknown`
/// means that there is no evidence either way. An `Evidence` is a value of
/// an answer, never a request failure. Combining evidence never raises it:
/// see [`and`](Evidence::and), and [`truth`](Evidence::truth) gives `True`
/// only for `Proved`.
///
/// ```
/// use kalyx::{Evidence, Truth};
///
/// let both = Evidence::Proved.and(Evidence::NumericEvidence);
/// assert_eq!(both, Evidence::NumericEvidence);
/// assert_eq!(both.truth(), Truth::Unknown);
/// ```
///
/// The enum is `#[non_exhaustive]`, so code outside the library matches it
/// with a wildcard arm; a `match` that lists the four variants and nothing
/// else does not compile:
///
/// ```compile_fail,E0004
/// use kalyx::Evidence;
///
/// fn decided(evidence: Evidence) -> bool {
///     match evidence {
///         Evidence::Proved | Evidence::Refuted => true,
///         Evidence::NumericEvidence | Evidence::Unknown => false,
///     }
/// }
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Evidence {
    /// The proposition is proved.
    Proved,
    /// The proposition is refuted: its negation is proved.
    Refuted,
    /// The proposition holds numerically; this is evidence, not a proof.
    NumericEvidence,
    /// There is no evidence either way.
    Unknown,
}

impl Evidence {
    /// The evidence of the conjunction of two propositions with the evidence
    /// `self` and `other`.
    ///
    /// One `Refuted` refutes the conjunction; otherwise one `Unknown` makes
    /// it `Unknown`; otherwise one `NumericEvidence` makes it
    /// `NumericEvidence`; and only two `Proved` prove it. So the result is
    /// never stronger than the weakest evidence that it needs: a conjunction
    /// is `Proved` exactly when both operands are. Takes no context and
    /// charges nothing.
    #[must_use]
    pub const fn and(self, other: Self) -> Self {
        match (self, other) {
            (Self::Refuted, _) | (_, Self::Refuted) => Self::Refuted,
            (Self::Unknown, _) | (_, Self::Unknown) => Self::Unknown,
            (Self::NumericEvidence, _) | (_, Self::NumericEvidence) => Self::NumericEvidence,
            (Self::Proved, Self::Proved) => Self::Proved,
        }
    }

    /// The truth value that the evidence establishes: `True` for `Proved`,
    /// `False` for `Refuted`, and `Unknown` for `NumericEvidence` and
    /// `Unknown`, since numerical evidence is not a proof. Takes no context
    /// and charges nothing.
    #[must_use]
    pub const fn truth(self) -> Truth {
        match self {
            Self::Proved => Truth::True,
            Self::Refuted => Truth::False,
            Self::NumericEvidence | Self::Unknown => Truth::Unknown,
        }
    }
}

/// A three-valued truth value: true, false or unknown.
///
/// `Unknown` means that the truth value was not decided; it carries no
/// information about which of the other two holds. A `Truth` is a value of
/// an answer, never a request failure, and [`and`](Truth::and) never turns
/// an `Unknown` into `True`.
///
/// ```
/// use kalyx::Truth;
///
/// assert_eq!(Truth::True.and(Truth::Unknown), Truth::Unknown);
/// assert_eq!(Truth::Unknown.and(Truth::False), Truth::False);
/// ```
///
/// The enum is `#[non_exhaustive]`, so code outside the library matches it
/// with a wildcard arm; a `match` that lists the three variants and nothing
/// else does not compile:
///
/// ```compile_fail,E0004
/// use kalyx::Truth;
///
/// fn known(truth: Truth) -> bool {
///     match truth {
///         Truth::True | Truth::False => true,
///         Truth::Unknown => false,
///     }
/// }
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Truth {
    /// The proposition holds.
    True,
    /// The proposition does not hold.
    False,
    /// The truth value was not decided.
    Unknown,
}

impl Truth {
    /// The strong Kleene conjunction of `self` and `other`: `False` when
    /// either is `False`, otherwise `Unknown` when either is `Unknown`, and
    /// `True` when both are `True`. Takes no context and charges nothing.
    ///
    /// A truth value that is decided component by component, such as a
    /// three-valued equality, is the conjunction of the components folded
    /// with this method, so one `Unknown` component without a `False` one
    /// keeps the whole `Unknown`.
    #[must_use]
    pub const fn and(self, other: Self) -> Self {
        match (self, other) {
            (Self::False, _) | (_, Self::False) => Self::False,
            (Self::Unknown, _) | (_, Self::Unknown) => Self::Unknown,
            (Self::True, Self::True) => Self::True,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Evidence, positive: each of the four kinds of evidence comes out of a
    // conjunction. No public entry of the library produces numerical
    // evidence yet, so this test gives it to the conjunction as an operand.
    #[test]
    fn each_evidence_comes_out_of_a_conjunction() {
        assert_eq!(Evidence::Proved.and(Evidence::Proved), Evidence::Proved);
        assert_eq!(Evidence::Refuted.and(Evidence::Proved), Evidence::Refuted);
        assert_eq!(Evidence::Proved.and(Evidence::Unknown), Evidence::Unknown);
        assert_eq!(
            Evidence::Proved.and(Evidence::NumericEvidence),
            Evidence::NumericEvidence
        );
    }

    // Truth, positive: each of the three truth values comes out of evidence.
    #[test]
    fn each_truth_comes_out_of_evidence() {
        assert_eq!(Evidence::Proved.truth(), Truth::True);
        assert_eq!(Evidence::Refuted.truth(), Truth::False);
        assert_eq!(Evidence::NumericEvidence.truth(), Truth::Unknown);
        assert_eq!(Evidence::Unknown.truth(), Truth::Unknown);
    }
}
