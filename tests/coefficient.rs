//! The coefficient-field trait under the property-testing tool of
//! `tests/field_properties/`, instantiated with `Rationals`, and the rules
//! of the trait for `Rationals`.
//!
//! The tool's checks are generic over its ring layer and its field layer;
//! `Rationals` enters both through the tool's wrapper of the library traits,
//! with the adapter and the model of `tests/field_properties/rationals.rs`,
//! a reduced fraction of two `i128`s with its own GCD. The ring axioms and
//! the field axioms are separate checks, and so are the agreement with the
//! model on small operands, the polynomials over $\mathbb{Q}$, the map
//! $\mathbb{Z} \to \mathbb{Q}$, the characteristic, and, on fixed inputs,
//! the work accounting and the cancellation of the operations of both
//! layers and of the arithmetic of the polynomials. Five families from
//! fixed seeds of the SplitMix64 sequence of
//! `tests/support/mod.rs` run 1,000 cases each against the model and 50
//! cases of large operands, checked by identities alone: associativity,
//! commutativity and distributivity on the ring layer, inverses and
//! canonical uniqueness on the field layer. A parent of the tests that is
//! not commutative, the rational quaternions, implements only the ring
//! layer, and the ring axioms fail on it at the commutativity of the
//! product.

#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    clippy::panic,
    reason = "the helpers of the tests unwrap their results and panic on a failed premise, as the tests do"
)]

mod field_properties;
mod support;

use std::convert::Infallible;

use kalyx::coefficient::{CoefficientField, CoefficientRing, Rationals, ZeroTest};
use kalyx::context::{CancelFlag, Storage, StorageCost};
use kalyx::number::{Integer, Rational};
use kalyx::{Context, ErrorKind, Limits, Result};

use field_properties::accounting::{Check, element_accounting, polynomial_accounting};
use field_properties::elements::{
    associativity, canonical_uniqueness, characteristic_zero, commutativity, commuting_paths,
    distributivity, field_axioms, field_model_agreement, homomorphism, inverses, ring_axioms,
    ring_model_agreement, zero_divisors,
};
use field_properties::rationals::{
    Fraction, INTEGERS, RATIONALS, accounting_elements, accounting_polynomials, canonical, gcd,
    polynomial_inputs, polynomial_ring, q, rationals, small_rationals,
};
use field_properties::univariate::{polynomial_laws, polynomial_model_agreement};
use field_properties::{Inspect, Integers, RingLayer, integer_of, pairs, triples};
use support::Sequence;

// ---------------------------------------------------------------------------
// The five families from fixed seeds

#[test]
fn rationals_are_associative() {
    associativity(&RATIONALS, 0x0A55_0C1A);
}

#[test]
fn rationals_are_commutative() {
    commutativity(&RATIONALS, 0xC033_07A7);
}

#[test]
fn rationals_are_distributive() {
    distributivity(&RATIONALS, 0xD157_7B07);
}

#[test]
fn rationals_have_inverses_and_zero_has_none() {
    inverses(&RATIONALS, 0x1A7E_25E5);
}

#[test]
fn rationals_have_unique_canonical_forms() {
    canonical_uniqueness(&RATIONALS, 0xCA10_0CA1);
}

#[test]
fn the_model_reduces_like_a_field_of_fractions() {
    assert_eq!(Fraction::new(6, -4), Fraction::new(-3, 2));
    assert_eq!(Fraction::new(0, -7).to_string(), "0");
    assert_eq!(Fraction::new(-10, 5).to_string(), "-2");
    assert_eq!(gcd(-12, 18), 6);
}

// ---------------------------------------------------------------------------
// The checks of the tool on the rationals

/// Ten fixed rationals and 64 generated ones of the eight kinds of
/// `rationals`, from small integers to integers of up to 200 bits,
/// fractions of 120-bit terms and dyadic fractions with denominators up to
/// $2^{130}$, with 2,000 drawn triples.
fn axiom_inputs() -> (Vec<Rational>, Vec<(usize, usize, usize)>) {
    let mut sequence = Sequence::new(0xC0EF_0001);
    let values = rationals(&mut sequence, 64);
    let triples = triples(values.len(), 2_000, &mut sequence);
    assert_eq!((values.len(), triples.len()), (74, 2_000));
    (values, triples)
}

#[test]
fn rationals_satisfy_the_ring_axioms() {
    let (values, triples) = axiom_inputs();
    ring_axioms(&RATIONALS, &values, &triples);
}

#[test]
fn rationals_satisfy_the_field_axioms() {
    let (values, triples) = axiom_inputs();
    field_axioms(&RATIONALS, &values, &triples);
    zero_divisors(&RATIONALS, &values);
}

#[test]
fn rationals_agree_with_the_small_model() {
    let mut sequence = Sequence::new(0xC0EF_0003);
    let values = small_rationals(&mut sequence, 40);
    let pairs = pairs(values.len(), 2_025, &mut sequence);
    assert_eq!((values.len(), pairs.len()), (45, 2_025));
    ring_model_agreement(&RATIONALS, &values, &pairs, &INTEGERS, 160);
    field_model_agreement(&RATIONALS, &values, &pairs);
}

#[test]
fn rational_polynomials_satisfy_the_polynomial_laws() {
    let ring = polynomial_ring();
    let mut sequence = Sequence::new(0xC0EF_0005);
    let polynomials = polynomial_inputs(&ring, &mut sequence, 40);
    let pairs = pairs(polynomials.len(), 600, &mut sequence);
    let triples = triples(polynomials.len(), 120, &mut sequence);
    assert_eq!(polynomials.len(), 41);
    assert!(polynomials.iter().all(|p| p.degree() <= Some(8)));
    polynomial_laws(&ring, &RATIONALS, &polynomials, &pairs, &triples);
}

#[test]
fn rational_polynomials_agree_with_the_coefficient_model() {
    let ring = polynomial_ring();
    let mut sequence = Sequence::new(0xC0EF_0006);
    let polynomials = polynomial_inputs(&ring, &mut sequence, 40);
    let pairs = pairs(polynomials.len(), 600, &mut sequence);
    polynomial_model_agreement(&ring, &RATIONALS, &polynomials, &pairs);
}

#[test]
fn integers_map_into_the_rationals() {
    let ring = RATIONALS.ring();
    let values: Vec<i128> = INTEGERS.iter().map(|&n| i128::from(n)).collect();
    let all = pairs(values.len(), 81, &mut Sequence::new(0));
    assert_eq!(all.len(), 81);
    homomorphism(
        &Integers,
        &RATIONALS,
        &|n: &i128, c: &mut Context| ring.from_integer(&integer_of(*n), c),
        &values,
        &all,
    );
    let from_integer = |n: &i64, c: &mut Context| ring.from_integer(&Integer::from(*n), c);
    let from =
        |n: &i64, _: &mut Context| -> Result<Rational> { Ok(Rational::from(Integer::from(*n))) };
    let new = |n: &i64, c: &mut Context| Rational::new(Integer::from(*n), Integer::from(1_i64), c);
    let literal = |n: &i64, c: &mut Context| {
        let magnitude = Rational::parse_decimal(&n.unsigned_abs().to_string(), c)?;
        if *n < 0 {
            magnitude.negate(c)
        } else {
            Ok(magnitude)
        }
    };
    commuting_paths(
        &RATIONALS,
        &INTEGERS,
        &[
            ("from_integer", &from_integer),
            ("Rational::from", &from),
            ("Rational::new", &new),
            ("Rational::parse_decimal", &literal),
        ],
    );
}

#[test]
fn rationals_have_characteristic_zero() {
    characteristic_zero(&RATIONALS, &INTEGERS);
}

/// The 68 runs of the accounting checks: 40 element operations and 28
/// polynomial operations.
fn accounting(check: Check) {
    let limits = Limits::new();
    let elements = accounting_elements();
    let ring = polynomial_ring();
    let polynomials = accounting_polynomials(&ring);
    let runs = element_accounting(check, &RATIONALS, &limits, &elements);
    assert_eq!(runs, 40);
    let factor = &elements[0].0;
    let runs = polynomial_accounting(check, &ring, &RATIONALS, &limits, factor, &polynomials);
    assert_eq!(runs, 28);
}

#[test]
fn rationals_are_charged_exactly_and_roll_back() {
    accounting(Check::Work);
}

#[test]
fn rationals_are_cancelled_at_every_charge_point() {
    accounting(Check::Cancellation);
}

// ---------------------------------------------------------------------------
// A parent that is not commutative

/// The rational quaternions $a + b i + c j + d k$, a ring with one that is
/// not commutative: $i j = k$ and $j i = -k$. It implements only the ring
/// layer of the tool, and its operations are those of `Rationals` through
/// the library trait.
struct Quaternions;

type Quaternion = [Rational; 4];

/// $\sum \pm x y$ over `terms`, each a sign and two factors.
fn signed_sum(terms: [(bool, &Rational, &Rational); 4], c: &mut Context) -> Result<Rational> {
    let mut sum = Rationals.zero(c)?;
    for (positive, x, y) in terms {
        let product = Rationals.multiply(x, y, c)?;
        sum = if positive {
            Rationals.add(&sum, &product, c)?
        } else {
            Rationals.subtract(&sum, &product, c)?
        };
    }
    Ok(sum)
}

impl Quaternions {
    fn embed(&self, real: Rational, c: &mut Context) -> Result<Quaternion> {
        Ok([
            real,
            Rationals.zero(c)?,
            Rationals.zero(c)?,
            Rationals.zero(c)?,
        ])
    }

    fn each(
        &self,
        a: &Quaternion,
        b: &Quaternion,
        c: &mut Context,
        step: fn(&Rational, &Rational, &mut Context) -> Result<Rational>,
    ) -> Result<Quaternion> {
        Ok([
            step(&a[0], &b[0], c)?,
            step(&a[1], &b[1], c)?,
            step(&a[2], &b[2], c)?,
            step(&a[3], &b[3], c)?,
        ])
    }
}

impl RingLayer for Quaternions {
    type Element = Quaternion;
    type Undecided = Infallible;

    fn zero(&self, c: &mut Context) -> Result<Quaternion> {
        let zero = Rationals.zero(c)?;
        self.embed(zero, c)
    }

    fn one(&self, c: &mut Context) -> Result<Quaternion> {
        let one = Rationals.one(c)?;
        self.embed(one, c)
    }

    fn from_integer(&self, n: &Integer, c: &mut Context) -> Result<Quaternion> {
        let real = Rationals.from_integer(n, c)?;
        self.embed(real, c)
    }

    fn negate(&self, a: &Quaternion, c: &mut Context) -> Result<Quaternion> {
        Ok([
            Rationals.negate(&a[0], c)?,
            Rationals.negate(&a[1], c)?,
            Rationals.negate(&a[2], c)?,
            Rationals.negate(&a[3], c)?,
        ])
    }

    fn add(&self, a: &Quaternion, b: &Quaternion, c: &mut Context) -> Result<Quaternion> {
        self.each(a, b, c, |x, y, c| Rationals.add(x, y, c))
    }

    fn subtract(&self, a: &Quaternion, b: &Quaternion, c: &mut Context) -> Result<Quaternion> {
        self.each(a, b, c, |x, y, c| Rationals.subtract(x, y, c))
    }

    /// The Hamilton product.
    fn multiply(&self, a: &Quaternion, b: &Quaternion, c: &mut Context) -> Result<Quaternion> {
        let [a1, b1, c1, d1] = a;
        let [a2, b2, c2, d2] = b;
        Ok([
            signed_sum(
                [
                    (true, a1, a2),
                    (false, b1, b2),
                    (false, c1, c2),
                    (false, d1, d2),
                ],
                c,
            )?,
            signed_sum(
                [
                    (true, a1, b2),
                    (true, b1, a2),
                    (true, c1, d2),
                    (false, d1, c2),
                ],
                c,
            )?,
            signed_sum(
                [
                    (true, a1, c2),
                    (false, b1, d2),
                    (true, c1, a2),
                    (true, d1, b2),
                ],
                c,
            )?,
            signed_sum(
                [
                    (true, a1, d2),
                    (true, b1, c2),
                    (false, c1, b2),
                    (true, d1, a2),
                ],
                c,
            )?,
        ])
    }

    fn zero_test(&self, a: &Quaternion, c: &mut Context) -> Result<ZeroTest<Infallible>> {
        for part in a {
            if Rationals.zero_test(part, c)? == ZeroTest::Nonzero {
                return Ok(ZeroTest::Nonzero);
            }
        }
        Ok(ZeroTest::Zero)
    }
}

/// The adapter of the quaternions: the stored form of a quaternion is that
/// of its four rational parts.
struct QuaternionAdapter;

impl Inspect for QuaternionAdapter {
    type Ring = Quaternions;

    fn ring(&self) -> &Quaternions {
        &Quaternions
    }

    fn label(&self) -> String {
        "the rational quaternions".into()
    }

    fn characteristic(&self) -> u64 {
        0
    }

    fn representation(&self, a: &Quaternion) -> String {
        format!("{a:?}")
    }

    fn canonical(&self, a: &Quaternion) -> bool {
        a.iter().all(canonical)
    }

    fn stored_zero(&self, a: &Quaternion) -> bool {
        a.iter().all(|part| part.numerator().is_zero())
    }
}

#[test]
#[should_panic(expected = "the rational quaternions: a b = b a fails")]
fn the_tool_rejects_a_noncommutative_parent() {
    let (zero, one) = (q(0, 1), q(1, 1));
    let unit = |k: usize| {
        let mut parts = [zero.clone(), zero.clone(), zero.clone(), zero.clone()];
        parts[k] = one.clone();
        parts
    };
    let elements = vec![
        unit(0),
        unit(1),
        unit(2),
        unit(3),
        [q(1, 2), q(1, 1), q(0, 1), q(-3, 1)],
        [zero.clone(), zero.clone(), zero.clone(), zero.clone()],
    ];
    let triples = triples(elements.len(), 216, &mut Sequence::new(0));
    assert_eq!(triples.len(), 216);
    ring_axioms(&QuaternionAdapter, &elements, &triples);
}

// ---------------------------------------------------------------------------
// The rules of the trait for `Rationals`

#[test]
fn rationals_decide_every_zero_test_without_a_charge() {
    let mut context = Context::new(Limits::new().with_max_work(0), CancelFlag::new());
    let q = Rationals;
    let zero = Rational::from(0_i64);
    let half = Rational::parse_decimal("0.5", &mut Context::new(Limits::new(), CancelFlag::new()))
        .unwrap();
    let answer: ZeroTest<Infallible> = q.zero_test(&zero, &mut context).unwrap();
    assert_eq!(answer, ZeroTest::Zero);
    assert_eq!(q.zero_test(&half, &mut context).unwrap(), ZeroTest::Nonzero);
    assert!(q.same_parent(&Rationals, &mut context).unwrap());
    assert_eq!(context.work_used(), 0);
}

#[test]
fn rationals_check_and_charge_new_elements() {
    let q = Rationals;
    let mut context = Context::new(Limits::new(), CancelFlag::new());
    assert_eq!(q.zero(&mut context).unwrap(), Rational::from(0_i64));
    assert_eq!(q.one(&mut context).unwrap(), Rational::from(1_i64));
    let n = Integer::from(-7_i64);
    assert_eq!(
        q.from_integer(&n, &mut context).unwrap(),
        Rational::from(n.clone())
    );
    assert_eq!(context.work_used(), 3);
    let mut narrow = Context::new(Limits::new().with_max_integer_bits(2), CancelFlag::new());
    let error = q.from_integer(&n, &mut narrow).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::ResourceLimit);
    assert_eq!(narrow.work_used(), 0);
    // The element operations charge one unit each, as those of `Rational`.
    let (a, b) = (Rational::from(3_i64), Rational::from(-2_i64));
    let before = context.work_used();
    q.negate(&a, &mut context).unwrap();
    q.add(&a, &b, &mut context).unwrap();
    q.subtract(&a, &b, &mut context).unwrap();
    q.multiply(&a, &b, &mut context).unwrap();
    q.inverse(&a, &mut context).unwrap();
    q.divide(&a, &b, &mut context).unwrap();
    assert_eq!(context.work_used(), before + 6);
    // A new element has at least 1 bit, its denominator.
    let mut none = Context::new(Limits::new().with_max_integer_bits(0), CancelFlag::new());
    assert_eq!(
        q.zero(&mut none).unwrap_err().kind(),
        ErrorKind::ResourceLimit
    );
    assert_eq!(
        q.one(&mut none).unwrap_err().kind(),
        ErrorKind::ResourceLimit
    );
    let zero = Integer::from(0_i64);
    assert_eq!(
        q.from_integer(&zero, &mut none).unwrap_err().kind(),
        ErrorKind::ResourceLimit
    );
    assert_eq!(none.work_used(), 0);
    assert_eq!(q, <Rationals as Default>::default());
}

// `measure` of `Rationals` is the storage cost of a rational, one node and
// |n| + |d| + 3 bytes for n/d, the value of `StorageCost`. Its signature
// takes the parent and the element and no context, so it neither charges
// nor fails: the work used after the samples are built does not change.
#[test]
fn rationals_measure_their_elements_by_the_storage_formula() {
    let measure: fn(&Rationals, &Rational) -> Storage = <Rationals as CoefficientRing>::measure;
    let q = Rationals;
    let mut context = Context::new(Limits::new(), CancelFlag::new());
    let huge = Integer::from(u64::MAX);
    let wide = q.from_integer(&huge, &mut context).unwrap();
    let wide = q.multiply(&wide, &wide, &mut context).unwrap();
    let small = Rational::new(Integer::from(-3_i64), Integer::from(4_i64), &mut context).unwrap();
    let tiny = q.inverse(&wide, &mut context).unwrap();
    let samples = [
        (Rational::from(0_i64), Storage::new(1, 4)),
        (Rational::from(1_i64), Storage::new(1, 5)),
        (Rational::from(-1_i64), Storage::new(1, 5)),
        (small, Storage::new(1, 2 + 3 + 3)),
        (Rational::from(i64::MIN), Storage::new(1, 64 + 1 + 3)),
        (wide.clone(), Storage::new(1, 128 + 1 + 3)),
        (tiny, Storage::new(1, 1 + 128 + 3)),
    ];
    let used = context.work_used();
    for (value, expected) in &samples {
        assert_eq!(measure(&q, value), *expected, "{value}");
        assert_eq!(q.measure(value), value.storage(), "{value}");
    }
    assert_eq!(context.work_used(), used);
    let sum = q.add(&wide, &Rational::from(1_i64), &mut context).unwrap();
    assert_eq!(q.measure(&sum), sum.storage());
}
