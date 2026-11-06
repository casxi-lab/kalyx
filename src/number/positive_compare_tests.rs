//! `Rational::compare` on positive rationals against the sign of the
//! subtraction, whose bound and charge it shares, and against an independent
//! `u128` oracle, at every small bit and work boundary and with 100,000-bit
//! operands.

use std::cmp::Ordering;

use num_bigint::BigInt;
use num_traits::One;

use super::arithmetic::canonical;
use super::*;
use crate::context::{CancelFlag, CancelProbe, Clock};
use crate::{ErrorKind, LimitExceeded, Limits};

/// What a comparison or a subtraction ended with: the order, or the kind and
/// the exceeded limit of the error.
type Outcome = std::result::Result<Ordering, (ErrorKind, Option<LimitExceeded>)>;

fn outcome(result: Result<Ordering>) -> Outcome {
    result.map_err(|error| (error.kind(), error.exceeded().cloned()))
}

/// The order by the sign of the difference.
fn reference(left: &Rational, right: &Rational, context: &mut Context) -> Outcome {
    outcome(left.subtract(right, context).map(|difference| {
        difference
            .numerator()
            .0
            .sign()
            .cmp(&num_bigint::Sign::NoSign)
    }))
}

fn compare(left: &Rational, right: &Rational, context: &mut Context) -> Outcome {
    outcome(left.compare(right, context))
}

fn context(bits: u64, work: u64) -> Context {
    Context::new(
        Limits::default()
            .with_max_integer_bits(bits)
            .with_max_work(work),
        CancelFlag::new(),
    )
}

fn q(numerator: BigInt, denominator: BigInt) -> Rational {
    Rational::from_canonical(canonical(&numerator, &denominator).unwrap())
}

fn bound(left: &Rational, right: &Rational) -> u64 {
    (left.numerator.bits() + right.denominator.bits())
        .max(right.numerator.bits() + left.denominator.bits())
        .saturating_add(1)
        .max(left.denominator.bits() + right.denominator.bits())
}

fn check_pair(left: &Rational, right: &Rational, expected: Ordering) {
    let original = (left.clone(), right.clone());
    let limit = bound(left, right);
    for bits in [0, limit - 1, limit, limit + 1] {
        for work in [0, 1, 2] {
            let mut old = context(bits, work);
            let mut new = context(bits, work);
            let actual = compare(left, right, &mut new);
            assert_eq!(actual, reference(left, right, &mut old));
            assert_eq!(old.work_used(), new.work_used());
            if work > 0 && bits >= limit {
                assert_eq!(actual, Ok(expected));
            }
        }
    }
    assert_eq!((left, right), (&original.0, &original.1));
}

#[test]
fn positive_comparison_matches_an_independent_small_integer_oracle() {
    // The oracle uses unreduced input integers and u128 arithmetic, independent
    // of the reduction and of the comparison of big integers.
    for a in 1_u64..=12 {
        for b in 1_u64..=12 {
            let left = q(a.into(), b.into());
            for c in 1_u64..=12 {
                for d in 1_u64..=12 {
                    let right = q(c.into(), d.into());
                    let expected =
                        (u128::from(a) * u128::from(d)).cmp(&(u128::from(c) * u128::from(b)));
                    let mut context = context(64, 1);
                    assert_eq!(compare(&left, &right, &mut context), Ok(expected));
                    assert_eq!(context.work_used(), 1);
                }
            }
        }
    }
}

#[test]
fn equal_adjacent_and_disjoint_product_bit_ranges_remain_exact() {
    for bits in [1_usize, 31, 32, 63, 64, 65, 127, 128, 1023, 4095] {
        let n = BigInt::one() << bits;
        let pairs = [
            // Cross-products differ by one despite overlapping bit ranges.
            (q(&n + 1, n.clone()), q(n.clone(), &n - 1), Ordering::Less),
            (q(&n - 1, &n + 1), q(&n + 1, &n + 3), Ordering::Less),
            (
                q(n.clone(), (&n << 1_usize) + 1),
                q((&n << 1_usize) - 1, (&n << 2_usize) + 1),
                Ordering::Greater,
            ),
            (q(1.into(), &n + 1), q(3.into(), &n + 1), Ordering::Less),
            (q(2.into(), &n * 6), q(3.into(), &n * 9), Ordering::Equal),
            (
                q(-&n, -BigInt::from(3)),
                q(&n * 2, 6.into()),
                Ordering::Equal,
            ),
        ];
        for (left, right, expected) in pairs {
            let (a, b) = left.parts();
            let (c, d) = right.parts();
            assert_eq!((a * d).cmp(&(c * b)), expected);
            check_pair(&left, &right, expected);
            check_pair(&right, &left, expected.reverse());
        }
    }
}

#[test]
fn hundred_thousand_bit_widths_preserve_the_subtraction_bound() {
    let n = BigInt::one() << 100_000_usize;
    let one = Rational::from(1_i64);
    let tiny = q(1.into(), n.clone());
    let huge = q(n.clone(), 1.into());
    for (left, right, expected) in [
        (&one, &tiny, Ordering::Greater),
        (&tiny, &one, Ordering::Less),
        (&huge, &tiny, Ordering::Greater),
        (&tiny, &huge, Ordering::Less),
    ] {
        let limit = bound(left, right);
        for bits in [limit - 1, limit, limit + 1] {
            let mut new = context(bits, 1);
            let actual = compare(left, right, &mut new);
            if bits < limit {
                let mut old = context(bits, 1);
                assert_eq!(actual, reference(left, right, &mut old));
                assert_eq!(new.work_used(), old.work_used());
                assert_eq!(new.work_used(), 0);
            } else {
                assert_eq!(actual, Ok(expected));
                assert_eq!(new.work_used(), 1);
            }
        }
    }
    // The near-neighbour case must use exact products, never a size heuristic.
    let left = q(&n + 1, n.clone());
    let right = q(n.clone(), &n - 1);
    let (a, b) = left.parts();
    let (c, d) = right.parts();
    assert_eq!((a * d).cmp(&(c * b)), Ordering::Less);
    assert_eq!(
        compare(&left, &right, &mut context(300_010, 1)),
        Ok(Ordering::Less)
    );
    // One successful huge subtraction is enough: the boundaries above do not
    // need to repeat its expensive reduction.
    let mut old = context(300_010, 1);
    let mut new = context(300_010, 1);
    assert_eq!(
        compare(&one, &tiny, &mut new),
        reference(&one, &tiny, &mut old)
    );
    assert_eq!(new.work_used(), old.work_used());
}

/// A clock that always reads the same time.
struct FixedClock(u64);

impl Clock for FixedClock {
    fn now(&mut self) -> u64 {
        self.0
    }

    fn fork(&self) -> Box<dyn Clock> {
        Box::new(FixedClock(self.0))
    }
}

/// A context with `limits`, cancelled or with an expired deadline as asked.
fn observed(limits: Limits, cancelled: bool, expired: bool) -> Context {
    let flag = CancelFlag::new();
    if cancelled {
        flag.cancel();
    }
    let probe: Box<dyn CancelProbe> = Box::new(flag);
    let context = Context::with_observers(limits, Box::new(FixedClock(10)), probe);
    if expired {
        context.with_deadline(5)
    } else {
        context
    }
}

#[test]
fn positive_comparison_preserves_every_small_bit_work_boundary_and_priority() {
    let pairs = [
        (q(1.into(), 3.into()), q(1.into(), 3.into())),
        (q(3.into(), 7.into()), q(5.into(), 11.into())),
        (q(1.into(), 127.into()), Rational::from(2_i64)),
    ];
    for (left, right) in pairs {
        let limit = bound(&left, &right);
        for bits in 0..=limit + 1 {
            for work in 0..=2 {
                let mut old = context(bits, work);
                let mut new = context(bits, work);
                assert_eq!(
                    compare(&left, &right, &mut new),
                    reference(&left, &right, &mut old)
                );
                assert_eq!(old.work_used(), new.work_used());
            }
        }
        // The bit bound is checked before the charge, so it takes precedence
        // over cancellation, an expired deadline and exhausted work, and with
        // enough bits these follow in the order of the context.
        for bits in [0, limit] {
            for cancelled in [false, true] {
                for expired in [false, true] {
                    let limits = Limits::default()
                        .with_max_integer_bits(bits)
                        .with_max_work(0);
                    let mut old = observed(limits, cancelled, expired);
                    let mut new = observed(limits, cancelled, expired);
                    let actual = compare(&left, &right, &mut new);
                    assert_eq!(actual, reference(&left, &right, &mut old));
                    assert_eq!(old.work_used(), 0);
                    assert_eq!(new.work_used(), 0);
                    let expected = if bits < limit {
                        ErrorKind::ResourceLimit
                    } else if cancelled {
                        ErrorKind::Cancelled
                    } else if expired {
                        ErrorKind::DeadlineExceeded
                    } else {
                        ErrorKind::ResourceLimit
                    };
                    let (kind, exceeded) = actual.unwrap_err();
                    assert_eq!(kind, expected);
                    if kind == ErrorKind::ResourceLimit {
                        let field = if bits < limit {
                            LimitField::IntegerBits
                        } else {
                            LimitField::Work
                        };
                        assert_eq!(exceeded.unwrap().id(), &crate::LimitId::Field(field));
                    }
                }
            }
        }
    }
}
