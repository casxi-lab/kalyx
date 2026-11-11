//! `Rational::compare` on positive rationals against a model of its rule,
//! which checks the bound of the cross products only when the pair needs
//! them and then charges one unit, and against an independent `u128` oracle,
//! at every small bit and work boundary and with 100,000-bit operands; and
//! the path that the comparison takes for one pair of each path.

use std::cmp::Ordering;

use num_bigint::BigInt;
use num_traits::One;

use super::arithmetic::{canonical, order_path};
use super::*;
use crate::context::{CancelFlag, CancelProbe, Clock};
use crate::{ErrorKind, LimitExceeded, Limits};

/// What a comparison or a subtraction ended with: the order, or the kind and
/// the exceeded limit of the error.
type Outcome = std::result::Result<Ordering, (ErrorKind, Option<LimitExceeded>)>;

fn outcome(result: Result<Ordering>) -> Outcome {
    result.map_err(|error| (error.kind(), error.exceeded().cloned()))
}

/// The bound of the cross products when `compare` must form them, by the
/// paths of the contract written out here: `None` for equal parts, different
/// signs, two power-of-two denominators, equal denominators, and sums
/// $|a| + |d|$ and $|c| + |b|$ of the bit lengths, which bound the bit
/// lengths of the cross products, that differ by at least two.
fn cross_bound(left: &Rational, right: &Rational) -> Option<u64> {
    let (a, b) = left.parts();
    let (c, d) = right.parts();
    let power_of_two = |x: &BigInt| x.magnitude().count_ones() == 1;
    if (a, b) == (c, d) || a.sign() != c.sign() || (power_of_two(b) && power_of_two(d)) || b == d {
        return None;
    }
    let first = a.bits() + d.bits();
    let second = c.bits() + b.bits();
    if first.abs_diff(second) >= 2 {
        None
    } else {
        Some(first.max(second))
    }
}

/// The order of the values, by the sign of the difference.
fn by_difference(left: &Rational, right: &Rational) -> Ordering {
    let mut wide = context(u64::MAX, 1);
    let difference = left.subtract(right, &mut wide).unwrap();
    difference
        .numerator()
        .0
        .sign()
        .cmp(&num_bigint::Sign::NoSign)
}

/// The outcome of the rule of the contract under a context in the same
/// state: the check of the bound of the cross products when the pair needs
/// them, then a charge of one unit, then the order of the values.
fn reference(left: &Rational, right: &Rational, context: &mut Context) -> Outcome {
    let checked = match cross_bound(left, right) {
        Some(bound) => context.check(LimitField::IntegerBits, bound),
        None => Ok(()),
    };
    let order = by_difference(left, right);
    outcome(checked.and_then(|()| context.charge(1)).map(|()| order))
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

/// The bound of a subtraction of the pair, which `compare` shared before it
/// checked only the bound of the cross products.
fn subtraction_bound(left: &Rational, right: &Rational) -> u64 {
    (left.numerator.bits() + right.denominator.bits())
        .max(right.numerator.bits() + left.denominator.bits())
        .saturating_add(1)
        .max(left.denominator.bits() + right.denominator.bits())
}

/// The bit limit around which a pair is tried: the bound of its cross
/// products, or the bound of its subtraction when a shortcut decides it, so
/// that a shortcut is tried where the subtraction is rejected.
fn boundary(left: &Rational, right: &Rational) -> u64 {
    cross_bound(left, right).unwrap_or_else(|| subtraction_bound(left, right))
}

fn check_pair(left: &Rational, right: &Rational, expected: Ordering) {
    let original = (left.clone(), right.clone());
    let limit = boundary(left, right);
    let checked = cross_bound(left, right).is_some();
    for bits in [0, limit - 1, limit, limit + 1] {
        for work in [0, 1, 2] {
            let mut model = context(bits, work);
            let mut new = context(bits, work);
            let actual = compare(left, right, &mut new);
            assert_eq!(actual, reference(left, right, &mut model));
            assert_eq!(model.work_used(), new.work_used());
            if work > 0 && (bits >= limit || !checked) {
                assert_eq!(actual, Ok(expected));
                assert_eq!(new.work_used(), 1);
            }
        }
    }
    assert_eq!((left, right), (&original.0, &original.1));
}

/// The path of one pair of each path at about 2,048 bits, and of sums of bit
/// lengths that differ by exactly two and by one. Equal parts share their
/// denominator, so equal denominators or the binary points of two equal
/// powers of two would give the same outcome, without a bound: no comparison
/// can tell the first path apart from them, and only the path shows that it
/// stops first.
#[test]
fn the_comparison_takes_the_first_path_that_applies() {
    let n = BigInt::one() << 2048_usize;
    let plus = |k: i64| &n + k;
    let e = q(plus(1), plus(-1));
    let pairs = [
        // Equal parts, also of two equal powers of two and of two zeros.
        (e.clone(), q(plus(1), plus(-1)), OrderPath::Same),
        (
            q(1.into(), n.clone()),
            q(1.into(), n.clone()),
            OrderPath::Same,
        ),
        (
            Rational::from(0_i64),
            Rational::from(0_i64),
            OrderPath::Same,
        ),
        (
            q(-plus(1), plus(-1)),
            e.clone(),
            OrderPath::Signs(Ordering::Less),
        ),
        (
            q(1.into(), BigInt::one() << 4095_usize),
            q(3.into(), BigInt::one() << 4000_usize),
            OrderPath::Dyadic(4095, 4000),
        ),
        (e.clone(), q(plus(3), plus(-1)), OrderPath::SameDenominator),
        // 2049 + 2048 and 1 + 2048 bits.
        (
            e.clone(),
            q(1.into(), plus(-3)),
            OrderPath::BitLengths(Ordering::Greater),
        ),
        // 2049 + 2049 and 2048 + 2048 bits.
        (
            e.clone(),
            q(plus(-3), plus(3)),
            OrderPath::BitLengths(Ordering::Greater),
        ),
        // 2049 + 2048 and 2048 + 2048 bits.
        (
            e.clone(),
            q(plus(-1), plus(-3)),
            OrderPath::CrossProducts(4097),
        ),
        (
            q(plus(-1), plus(-3)),
            q(plus(-3), plus(-5)),
            OrderPath::CrossProducts(4096),
        ),
    ];
    for (left, right, path) in &pairs {
        assert_eq!(order_path(left.parts(), right.parts()), *path);
    }
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
            // For odd `bits` above 1, 3 divides n + 1, and the sums of the
            // bit lengths, `bits` and `bits` + 2, differ by exactly two; at
            // `bits` = 1 the second operand reduces to 1 and the pair takes
            // the cross products.
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
fn hundred_thousand_bit_widths_check_only_the_bound_of_the_cross_products() {
    let n = BigInt::one() << 100_000_usize;
    let one = Rational::from(1_i64);
    let tiny = q(1.into(), n.clone());
    let huge = q(n.clone(), 1.into());
    // Power-of-two denominators align their binary points: no bound is
    // checked, even where the subtraction is rejected before any charge.
    for (left, right, expected) in [
        (&one, &tiny, Ordering::Greater),
        (&tiny, &one, Ordering::Less),
        (&huge, &tiny, Ordering::Greater),
        (&tiny, &huge, Ordering::Less),
    ] {
        assert_eq!(cross_bound(left, right), None);
        let limit = subtraction_bound(left, right);
        let mut rejected = context(limit - 1, 1);
        let (kind, exceeded) =
            outcome(left.subtract(right, &mut rejected).map(|_| Ordering::Equal)).unwrap_err();
        assert_eq!(kind, ErrorKind::ResourceLimit);
        assert_eq!(
            exceeded.unwrap().amount(),
            crate::LimitAmount::Required(limit)
        );
        assert_eq!(rejected.work_used(), 0);
        for bits in [0, limit - 1, limit, limit + 1] {
            let mut new = context(bits, 1);
            assert_eq!(compare(left, right, &mut new), Ok(expected));
            assert_eq!(new.work_used(), 1);
        }
    }
    // The near-neighbour case must use exact products, never a size
    // heuristic, and checks their bound on both sides.
    let left = q(&n + 1, n.clone());
    let right = q(n.clone(), &n - 1);
    let (a, b) = left.parts();
    let (c, d) = right.parts();
    assert_eq!((a * d).cmp(&(c * b)), Ordering::Less);
    let limit = cross_bound(&left, &right).unwrap();
    assert_eq!(limit, 200_002);
    for bits in [limit - 1, limit, limit + 1] {
        let mut model = context(bits, 1);
        let mut new = context(bits, 1);
        let actual = compare(&left, &right, &mut new);
        assert_eq!(actual, reference(&left, &right, &mut model));
        assert_eq!(new.work_used(), model.work_used());
        if bits >= limit {
            assert_eq!(actual, Ok(Ordering::Less));
            assert_eq!(new.work_used(), 1);
        } else {
            assert_eq!(new.work_used(), 0);
        }
    }
    // Equal parts decide under every `max_integer_bits`, at any width.
    let copy = q(&n + 1, n.clone());
    let mut none = context(0, 1);
    assert_eq!(compare(&left, &copy, &mut none), Ok(Ordering::Equal));
    assert_eq!(none.work_used(), 1);
    // One successful huge subtraction is enough to check the order of a
    // dyadic pair against the sign of the difference.
    assert_eq!(
        compare(&one, &tiny, &mut context(0, 1)),
        Ok(by_difference(&one, &tiny))
    );
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
    // Equal parts, cross products, sums of bit lengths that differ by seven
    // and by exactly two (5 and 3 bits for 5/3 and 1/2), power-of-two
    // denominators and equal denominators.
    let pairs = [
        (q(1.into(), 3.into()), q(1.into(), 3.into())),
        (q(3.into(), 7.into()), q(5.into(), 11.into())),
        (q(1.into(), 127.into()), Rational::from(2_i64)),
        (q(5.into(), 3.into()), q(1.into(), 2.into())),
        (q(1.into(), 4.into()), q(3.into(), 8.into())),
        (q(1.into(), 5.into()), q(2.into(), 5.into())),
    ];
    for (left, right) in pairs {
        let limit = boundary(&left, &right);
        let checked = cross_bound(&left, &right).is_some();
        for bits in 0..=limit + 1 {
            for work in 0..=2 {
                let mut model = context(bits, work);
                let mut new = context(bits, work);
                assert_eq!(
                    compare(&left, &right, &mut new),
                    reference(&left, &right, &mut model)
                );
                assert_eq!(model.work_used(), new.work_used());
            }
        }
        // The bit bound of the cross products is checked before the charge,
        // so it takes precedence over cancellation, an expired deadline and
        // exhausted work; a shortcut checks no bound; and with enough bits
        // these follow in the order of the context.
        for bits in [0, limit] {
            for cancelled in [false, true] {
                for expired in [false, true] {
                    let limits = Limits::default()
                        .with_max_integer_bits(bits)
                        .with_max_work(0);
                    let mut model = observed(limits, cancelled, expired);
                    let mut new = observed(limits, cancelled, expired);
                    let actual = compare(&left, &right, &mut new);
                    assert_eq!(actual, reference(&left, &right, &mut model));
                    assert_eq!(model.work_used(), 0);
                    assert_eq!(new.work_used(), 0);
                    let by_bits = checked && bits < limit;
                    let expected = if by_bits {
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
                        let field = if by_bits {
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
