//! The power-of-two paths of the kernels against the general reduction of
//! num-rational, on seeded operands, including unreduced inputs and signed
//! power-of-two divisors; every operation charges the same work on every
//! path.

use std::cmp::Ordering;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use super::arithmetic::{
    ArithmeticOperation, Parts, canonical, dyadic, dyadic_binary, dyadic_cmp, dyadic_exponent,
};
use super::*;
use crate::context::CancelFlag;
use crate::{ErrorKind, Limits};

fn context() -> Context {
    Context::new(Limits::default(), CancelFlag::new())
}

/// A fixed linear congruential sequence; the tests need no external generator.
struct Sequence(u64);

impl Sequence {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 11
    }

    fn integer(&mut self) -> BigInt {
        let limbs = self.next() % 4;
        let mut value = BigInt::from(self.next() % 1000);
        for _ in 0..limbs {
            value = (value << 61_usize) + BigInt::from(self.next());
        }
        // Exercise trailing zeros in the numerator as well as odd values.
        value <<= self.next() % 5;
        if self.next().is_multiple_of(2) {
            -value
        } else {
            value
        }
    }

    fn dyadic(&mut self) -> Rational {
        let exponent = [0_u64, 0, 1, 2, 7, 63, 64, 65, 130][(self.next() % 9) as usize];
        rational(self.integer(), BigInt::one() << exponent)
    }
}

/// The canonical rational $n / d$.
fn rational(numerator: BigInt, denominator: BigInt) -> Rational {
    Rational::from_canonical(canonical(&numerator, &denominator).unwrap())
}

fn small(numerator: i64, denominator: i64) -> Rational {
    rational(numerator.into(), denominator.into())
}

/// The value of a rational in num-rational, the reference of these tests.
fn reference(value: &Rational) -> BigRational {
    BigRational::new(value.numerator.0.clone(), value.denominator.0.clone())
}

fn parts_of(value: &BigRational) -> Parts {
    (value.numer().clone(), value.denom().clone())
}

/// The machine words $\max(1, \lceil b / 64 \rceil)$ of a rational whose
/// larger part has $b$ bits, computed here: a product and a quotient charge
/// the product of the words of their operands.
fn word_count(value: &Rational) -> u64 {
    let bits = value.numerator.0.bits().max(value.denominator.0.bits());
    bits.div_ceil(64).max(1)
}

fn canonical_form(parts: &Parts) -> bool {
    let reduced = BigRational::new(parts.0.clone(), parts.1.clone());
    parts.1.is_positive() && &parts.0 == reduced.numer() && &parts.1 == reduced.denom()
}

#[test]
fn recognizes_only_positive_powers_of_two() {
    assert_eq!(dyadic_exponent(&BigInt::from(1)), Some(0));
    assert_eq!(dyadic_exponent(&BigInt::from(8)), Some(3));
    assert_eq!(dyadic_exponent(&BigInt::from(3)), None);
    assert_eq!(dyadic_exponent(&BigInt::from(12)), None);
    assert_eq!(dyadic_exponent(&BigInt::from(-8)), None);
    assert_eq!(dyadic_exponent(&BigInt::from(0)), None);
    assert_eq!(dyadic_exponent(&(BigInt::one() << 200_u32)), Some(200));
}

#[test]
fn normalization_removes_exactly_the_shared_powers_of_two() {
    for (numerator, exponent, expected) in [
        (0_i64, 9_u64, (0_i64, 1_i64)),
        (12, 0, (12, 1)),
        (12, 1, (6, 1)),
        (12, 2, (3, 1)),
        (12, 5, (3, 8)),
        (-40, 4, (-5, 2)),
        (7, 3, (7, 8)),
    ] {
        let value = dyadic(numerator.into(), exponent);
        assert_eq!(value, (expected.0.into(), expected.1.into()));
    }
}

#[test]
fn ring_operations_match_the_general_reduction() {
    let mut sequence = Sequence(0x0CA5_2026);
    let mut wide_products = 0;
    for _ in 0..4000 {
        let (left, right) = (sequence.dyadic(), sequence.dyadic());
        let (l, r) = (reference(&left), reference(&right));
        for operation in [
            ArithmeticOperation::Add,
            ArithmeticOperation::Subtract,
            ArithmeticOperation::Multiply,
        ] {
            let expected = match operation {
                ArithmeticOperation::Add => &l + &r,
                ArithmeticOperation::Subtract => &l - &r,
                _ => &l * &r,
            };
            let actual = dyadic_binary(left.parts(), right.parts(), operation).unwrap();
            assert!(canonical_form(&actual));
            assert_eq!(actual, parts_of(&expected));
            // Every entry point returns the same value on this path, and the
            // charge of the table of the contract: one unit for a sum and a
            // difference, the product of the words for a product.
            let mut c = context();
            let (value, charge) = match operation {
                ArithmeticOperation::Add => (left.add(&right, &mut c), 1),
                ArithmeticOperation::Subtract => (left.subtract(&right, &mut c), 1),
                _ => (
                    left.multiply(&right, &mut c),
                    word_count(&left) * word_count(&right),
                ),
            };
            let value = value.unwrap();
            assert_eq!(value.parts(), (expected.numer(), expected.denom()));
            assert_eq!(c.work_used(), charge);
            if charge > 1 {
                wide_products += 1;
            }
        }
        assert_eq!(dyadic_cmp(left.parts(), right.parts()), Some(l.cmp(&r)));
        assert_eq!(left.compare(&right, &mut context()).unwrap(), l.cmp(&r));
    }
    // Numerators of up to about 200 bits and denominators up to 2^130 give
    // products of operands of several words.
    assert!(wide_products > 1000, "{wide_products}");
}

#[test]
fn unreduced_dyadic_operands_still_produce_canonical_values() {
    let (six, eight, ten, four) = (
        BigInt::from(6),
        BigInt::from(8),
        BigInt::from(10),
        BigInt::from(4),
    );
    let left = (&six, &eight);
    let right = (&ten, &four);
    let sum = dyadic_binary(left, right, ArithmeticOperation::Add).unwrap();
    assert_eq!(sum, (13.into(), 4.into()));
    let product = dyadic_binary(left, right, ArithmeticOperation::Multiply).unwrap();
    assert_eq!(product, (15.into(), 8.into()));
    assert_eq!(dyadic_cmp(left, right), Some(Ordering::Less));
}

#[test]
fn division_by_a_signed_power_of_two_matches_the_general_quotient() {
    let mut sequence = Sequence(0x0D17_1DE5);
    let mut wide_quotients = 0;
    for _ in 0..3000 {
        let left = sequence.dyadic();
        let shift = [0_usize, 1, 2, 9, 64, 70][(sequence.next() % 6) as usize];
        let exponent = [0_usize, 0, 1, 5, 66][(sequence.next() % 5) as usize];
        let sign = if sequence.next().is_multiple_of(2) {
            1
        } else {
            -1
        };
        let right = rational(BigInt::from(sign) << shift, BigInt::one() << exponent);
        let expected = reference(&left) / reference(&right);
        let actual =
            dyadic_binary(left.parts(), right.parts(), ArithmeticOperation::Divide).unwrap();
        assert!(canonical_form(&actual));
        assert_eq!(actual, parts_of(&expected));
        let mut c = context();
        let value = left.divide(&right, &mut c).unwrap();
        assert_eq!(value.parts(), (expected.numer(), expected.denom()));
        // The charge of a quotient: the product of the words.
        let charge = word_count(&left) * word_count(&right);
        assert_eq!(c.work_used(), charge);
        if charge > 1 {
            wide_quotients += 1;
        }
    }
    assert!(wide_quotients > 1000, "{wide_quotients}");
}

#[test]
fn integer_halving_and_zero_divisors_keep_their_results_and_errors() {
    for (n, d, expected) in [
        (7_i64, 2_i64, (7_i64, 2_i64)),
        (8, 2, (4, 1)),
        (-6, 4, (-3, 2)),
        (6, -4, (-3, 2)),
        (0, 8, (0, 1)),
        (5, 1, (5, 1)),
        (5, -1, (-5, 1)),
        (9, 6, (3, 2)),
    ] {
        let mut c = context();
        let value = Rational::from(n)
            .divide(&Rational::from(d), &mut c)
            .unwrap();
        assert_eq!(value, small(expected.0, expected.1));
        assert_eq!(c.work_used(), 1);
    }
    let half = small(1, 2);
    let zero = Rational::from(0_i64);
    assert!(dyadic_binary(half.parts(), zero.parts(), ArithmeticOperation::Divide).is_none());
    let mut c = context();
    let error = half.divide(&zero, &mut c).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::DivisionByZero));
    // The divisor is tested before any charge.
    assert_eq!(c.work_used(), 0);
}

#[test]
fn canonical_values_match_the_general_reduction() {
    for (n, d) in [
        (6_i64, 8_i64),
        (-10, 4),
        (0, 16),
        (7, 1),
        (9, 12),
        (-5, 3),
        (4, -8),
        (3, -9),
    ] {
        let expected = BigRational::new(n.into(), d.into());
        let value = canonical(&n.into(), &d.into()).unwrap();
        assert_eq!(value, parts_of(&expected));
    }
    assert_eq!(
        canonical(&1.into(), &BigInt::zero()).unwrap_err().kind(),
        ErrorKind::Fault(FaultKind::Internal)
    );
}

#[test]
fn other_operands_use_the_general_path() {
    let third = small(1, 3);
    let half = small(1, 2);
    let three_quarters = small(3, 4);
    assert!(dyadic_binary(third.parts(), half.parts(), ArithmeticOperation::Add).is_none());
    assert!(dyadic_binary(half.parts(), third.parts(), ArithmeticOperation::Multiply).is_none());
    assert!(dyadic_binary(half.parts(), third.parts(), ArithmeticOperation::Divide).is_none());
    assert!(
        dyadic_binary(
            half.parts(),
            three_quarters.parts(),
            ArithmeticOperation::Divide
        )
        .is_none()
    );
    assert!(dyadic_cmp(third.parts(), half.parts()).is_none());
    let mut c = context();
    assert_eq!(third.add(&half, &mut c).unwrap(), small(5, 6));
    assert_eq!(half.divide(&third, &mut c).unwrap(), small(3, 2));
    assert_eq!(half.divide(&half, &mut c).unwrap(), Rational::from(1_i64));
    assert_eq!(c.work_used(), 3);
}
