//! The shared result types, `Evidence` and `Truth`, as code outside the
//! library sees them: the negative cases of their combinations. No public
//! entry of the library produces numerical evidence yet, so these tests
//! build every variant themselves and give it to the combinations.

use kalyx::{Evidence, Truth};

const EVIDENCE: [Evidence; 4] = [
    Evidence::Proved,
    Evidence::Refuted,
    Evidence::NumericEvidence,
    Evidence::Unknown,
];

// The conjunction of `left` and `right` by the rule of the contract, written
// apart from `Evidence::and`: one `Refuted` refutes it; otherwise one
// `Unknown` makes it `Unknown`; otherwise one `NumericEvidence` makes it
// `NumericEvidence`; otherwise both are `Proved`, and so is the conjunction.
fn conjunction_by_the_rule(left: Evidence, right: Evidence) -> Evidence {
    let either = |evidence| left == evidence || right == evidence;
    if either(Evidence::Refuted) {
        Evidence::Refuted
    } else if either(Evidence::Unknown) {
        Evidence::Unknown
    } else if either(Evidence::NumericEvidence) {
        Evidence::NumericEvidence
    } else {
        Evidence::Proved
    }
}

// Negative: over all 16 pairs, a conjunction of evidence is proved only when
// both operands are proved and refuted exactly when one of them is refuted,
// and the truth value of a conjunction of evidence is the conjunction of
// the truth values of its operands. Each pair, in either order, also gives
// the conjunction of the rule, so neither `Unknown` nor `NumericEvidence`
// turns into the other.
#[test]
fn combining_evidence_never_raises_its_level() {
    let mut pairs = 0;
    for left in EVIDENCE {
        for right in EVIDENCE {
            let both = left.and(right);
            let proved = left == Evidence::Proved && right == Evidence::Proved;
            let refuted = left == Evidence::Refuted || right == Evidence::Refuted;
            assert_eq!(both == Evidence::Proved, proved, "{left:?} and {right:?}");
            assert_eq!(both == Evidence::Refuted, refuted, "{left:?} and {right:?}");
            assert_eq!(
                both.truth(),
                left.truth().and(right.truth()),
                "{left:?} and {right:?}"
            );
            assert_eq!(
                both,
                conjunction_by_the_rule(left, right),
                "{left:?} and {right:?}"
            );
            assert_eq!(both, right.and(left), "{left:?} and {right:?}");
            pairs += 1;
        }
    }
    assert_eq!(pairs, 16);
}

// Negative: numerical evidence is never a proof. Its truth value is
// unknown, and its conjunction with any evidence, on either side, is
// neither proved nor true.
#[test]
fn numerical_evidence_never_becomes_proved_or_true() {
    assert_eq!(Evidence::NumericEvidence.truth(), Truth::Unknown);
    for other in EVIDENCE {
        for both in [
            Evidence::NumericEvidence.and(other),
            other.and(Evidence::NumericEvidence),
        ] {
            assert_ne!(both, Evidence::Proved, "{other:?}");
            assert_ne!(both.truth(), Truth::True, "{other:?}");
        }
    }
}

// Negative: a three-valued equality folds the truth values of its
// components by the conjunction of `Truth`, so one unknown component among
// true ones keeps the equality unknown, and an unknown stays unknown in a
// conjunction with a true or an unknown value.
#[test]
fn an_unknown_from_three_valued_equality_is_never_promoted() {
    let components = [Truth::True, Truth::Unknown, Truth::True];
    let mut equal = Truth::True;
    for component in components {
        equal = equal.and(component);
    }
    assert_eq!(equal, Truth::Unknown);
    for other in [Truth::True, Truth::Unknown] {
        assert_eq!(Truth::Unknown.and(other), Truth::Unknown, "{other:?}");
        assert_eq!(other.and(Truth::Unknown), Truth::Unknown, "{other:?}");
    }
}
