//! The coefficient-field trait under the property-testing tool of
//! `tests/field_properties/`, instantiated with `Rationals` and with the
//! prime fields `PrimeField` of five primes, and the rules of the trait for
//! both.
//!
//! The tool's checks are generic over its ring layer and its field layer;
//! a parent enters both through the tool's wrapper of the library traits,
//! with an adapter and a model: for `Rationals` those of
//! `tests/field_properties/rationals.rs`, a reduced fraction of two `i128`s
//! with its own GCD, and for $\mathbb F_p$ with $p$ = 2, 3, 7, 65537 and
//! 4294967291 those of `tests/field_properties/primes.rs`, residues with
//! their own inverse. The ring axioms and the field axioms are separate
//! checks, and so are the agreement with the model on small operands, the
//! polynomials over the field, the map from the integers, the
//! characteristic, zero or $p$ with $(a + b)^p = a^p + b^p$, and, on fixed
//! inputs, the work accounting and the cancellation of the operations of
//! both layers and of the arithmetic of the polynomials. Five families from
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

use kalyx::coefficient::{
    CoefficientField, CoefficientRing, PrimeField, PrimeResidue, Rationals, ZeroTest,
};
use kalyx::context::{CancelFlag, Storage, StorageCost};
use kalyx::number::{Integer, Rational};
use kalyx::{Context, Error, ErrorKind, FaultKind, LimitField, LimitId, Limits, Result};

use field_properties::accounting::{
    Check, Run, cancellation, element_accounting, polynomial_accounting, work_accounting,
};
use field_properties::elements::{
    additive_frobenius, associativity, canonical_uniqueness, characteristic_prime,
    characteristic_zero, commutativity, commuting_paths, distributivity, field_axioms,
    field_model_agreement, homomorphism, inverses, ring_axioms, ring_model_agreement,
    zero_divisors,
};
use field_properties::primes::{self, PRIMES, PrimeAdapter};
use field_properties::rationals::{
    Fraction, INTEGERS, RATIONALS, accounting_elements, accounting_polynomials, canonical, gcd,
    polynomial_inputs, polynomial_ring, q, rationals, small_rationals,
};
use field_properties::univariate::{polynomial_laws, polynomial_model_agreement};
use field_properties::{Inspect, Integers, RingLayer, integer_of, pairs, roomy, triples};
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
/// fractions of terms of up to 120 bits and dyadic fractions with
/// denominators up to $2^{130}$, with 2,000 drawn triples.
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
    // The element operations charge one unit each on these one-word
    // operands, as those of `Rational` do.
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

// ---------------------------------------------------------------------------
// The prime fields under the tool

/// The adapters of the five primes of the checks.
fn prime_fields() -> Vec<PrimeAdapter> {
    PRIMES.iter().map(|&p| PrimeAdapter::new(p)).collect()
}

/// `p` as a count, for a small prime.
fn count(p: u64) -> usize {
    usize::try_from(p).unwrap()
}

#[test]
fn prime_fields_are_associative() {
    for field in prime_fields() {
        associativity(&field, 0x0A55_0C1A);
    }
}

#[test]
fn prime_fields_are_commutative() {
    for field in prime_fields() {
        commutativity(&field, 0xC033_07A7);
    }
}

#[test]
fn prime_fields_are_distributive() {
    for field in prime_fields() {
        distributivity(&field, 0xD157_7B07);
    }
}

#[test]
fn prime_fields_have_inverses_and_zero_has_none() {
    for field in prime_fields() {
        inverses(&field, 0x1A7E_25E5);
    }
}

#[test]
fn prime_fields_have_unique_canonical_forms() {
    for field in prime_fields() {
        canonical_uniqueness(&field, 0xCA10_0CA1);
    }
}

/// The inputs of the axioms of $\mathbb F_p$: for $p \le 7$ every residue
/// and every triple, otherwise the seven fixed residues and 64 drawn ones
/// with 2,000 drawn triples.
fn prime_axiom_inputs(
    field: &PrimeAdapter,
    sequence: &mut Sequence,
) -> (Vec<PrimeResidue>, Vec<(usize, usize, usize)>) {
    let p = field.modulus();
    let values = primes::elements(field, &primes::residues(p, 7, 64, sequence));
    let triples = triples(values.len(), 2_000, sequence);
    let expected = if p <= 7 {
        (count(p), count(p).pow(3))
    } else {
        (71, 2_000)
    };
    assert_eq!((values.len(), triples.len()), expected);
    (values, triples)
}

#[test]
fn prime_fields_satisfy_the_ring_axioms() {
    let mut sequence = Sequence::new(0xC0EF_0201);
    for field in prime_fields() {
        let (values, triples) = prime_axiom_inputs(&field, &mut sequence);
        ring_axioms(&field, &values, &triples);
    }
}

#[test]
fn prime_fields_satisfy_the_field_axioms() {
    let mut sequence = Sequence::new(0xC0EF_0201);
    for field in prime_fields() {
        let (values, triples) = prime_axiom_inputs(&field, &mut sequence);
        field_axioms(&field, &values, &triples);
        zero_divisors(&field, &values);
    }
}

#[test]
fn prime_fields_agree_with_the_small_model() {
    let mut sequence = Sequence::new(0xC0EF_0203);
    for field in prime_fields() {
        let p = field.modulus();
        let values = primes::elements(&field, &primes::residues(p, 5, 40, &mut sequence));
        let pairs = pairs(values.len(), 2_025, &mut sequence);
        let integers = primes::integers(p);
        let size = if p <= 7 { count(p) } else { 45 };
        assert_eq!(
            (values.len(), pairs.len(), integers.len()),
            (size, size * size, 12)
        );
        ring_model_agreement(&field, &values, &pairs, &integers, 160);
        field_model_agreement(&field, &values, &pairs);
    }
}

#[test]
fn prime_field_polynomials_satisfy_the_polynomial_laws() {
    let mut sequence = Sequence::new(0xC0EF_0205);
    for field in prime_fields() {
        let ring = primes::polynomial_ring(&field);
        let polynomials = primes::polynomial_inputs(&ring, &field, &mut sequence, 40);
        let pairs = pairs(polynomials.len(), 600, &mut sequence);
        let triples = triples(polynomials.len(), 120, &mut sequence);
        assert_eq!(
            (polynomials.len(), pairs.len(), triples.len()),
            (41, 600, 120)
        );
        assert!(polynomials.iter().all(|p| p.degree() <= Some(8)));
        polynomial_laws(&ring, &field, &polynomials, &pairs, &triples);
    }
}

#[test]
fn prime_field_polynomials_agree_with_the_coefficient_model() {
    let mut sequence = Sequence::new(0xC0EF_0206);
    for field in prime_fields() {
        let ring = primes::polynomial_ring(&field);
        let polynomials = primes::polynomial_inputs(&ring, &field, &mut sequence, 40);
        let pairs = pairs(polynomials.len(), 600, &mut sequence);
        assert_eq!((polynomials.len(), pairs.len()), (41, 600));
        polynomial_model_agreement(&ring, &field, &polynomials, &pairs);
    }
}

/// Every pair of the polynomials of degree at most 3 over $\mathbb F_2$
/// and at most 2 over $\mathbb F_3$, the zero polynomial included, under
/// the polynomial laws, with 200 drawn triples, and against the model.
#[test]
fn every_small_polynomial_pair_satisfies_the_laws() {
    let mut sequence = Sequence::new(0xC0EF_0207);
    for (p, max_degree) in [(2, 3), (3, 2)] {
        let field = PrimeAdapter::new(p);
        let ring = primes::polynomial_ring(&field);
        let polynomials = primes::every_polynomial(&ring, &field, max_degree);
        let size = polynomials.len();
        let pairs = pairs(size, size * size, &mut sequence);
        let triples = triples(size, 200, &mut sequence);
        let expected = usize::try_from(p.pow(max_degree + 1)).unwrap();
        assert_eq!(
            (size, pairs.len(), triples.len()),
            (expected, expected * expected, 200)
        );
        polynomial_laws(&ring, &field, &polynomials, &pairs, &triples);
        polynomial_model_agreement(&ring, &field, &polynomials, &pairs);
    }
}

#[test]
fn integers_map_into_the_prime_fields() {
    for field in prime_fields() {
        let p = field.modulus();
        let ring = field.ring();
        let values: Vec<i128> = primes::integers(p).into_iter().map(i128::from).collect();
        let all = pairs(values.len(), 144, &mut Sequence::new(0));
        assert_eq!(all.len(), 144);
        homomorphism(
            &Integers,
            &field,
            &|n: &i128, c: &mut Context| ring.from_integer(&integer_of(*n), c),
            &values,
            &all,
        );
        let mut wide = values.clone();
        wide.push(1 << 100);
        assert_eq!(wide.len(), 13);
        let modulus = i128::from(p);
        let from_integer = |n: &i128, c: &mut Context| ring.from_integer(&integer_of(*n), c);
        let reduced =
            |n: &i128, c: &mut Context| ring.from_integer(&integer_of(n.rem_euclid(modulus)), c);
        let negated = |n: &i128, c: &mut Context| {
            let opposite = integer_of(*n).negate(c)?;
            let image = ring.from_integer(&opposite, c)?;
            ring.negate(&image, c)
        };
        commuting_paths(
            &field,
            &wide,
            &[
                ("from_integer", &from_integer),
                ("n mod p", &reduced),
                ("-(-n)", &negated),
            ],
        );
    }
}

#[test]
fn prime_fields_have_characteristic_p() {
    for field in prime_fields() {
        let integers = primes::integers(field.modulus());
        assert_eq!(integers.len(), 12);
        characteristic_prime(&field, &integers);
    }
}

#[test]
fn sums_raised_to_the_characteristic_are_sums_of_powers() {
    let mut sequence = Sequence::new(0xC0EF_0204);
    for field in prime_fields() {
        let p = field.modulus();
        let values = primes::elements(&field, &primes::residues(p, 7, 24, &mut sequence));
        let pairs = pairs(values.len(), 600, &mut sequence);
        let expected = if p <= 7 {
            (count(p), count(p) * count(p))
        } else {
            (31, 600)
        };
        assert_eq!((values.len(), pairs.len()), expected);
        additive_frobenius(&field, &values, &pairs);
    }
}

/// The 340 runs of the accounting checks: for each of the five primes, 40
/// element operations and 28 polynomial operations.
fn prime_accounting(check: Check) {
    let limits = Limits::new();
    for field in prime_fields() {
        let elements = primes::accounting_elements(&field);
        let ring = primes::polynomial_ring(&field);
        let polynomials = primes::accounting_polynomials(&ring, &field);
        let runs = element_accounting(check, &field, &limits, &elements);
        assert_eq!(runs, 40);
        let factor = &elements[0].0;
        let runs = polynomial_accounting(check, &ring, &field, &limits, factor, &polynomials);
        assert_eq!(runs, 28);
    }
}

#[test]
fn prime_fields_are_charged_exactly_and_roll_back() {
    prime_accounting(Check::Work);
}

#[test]
fn prime_fields_are_cancelled_at_every_charge_point() {
    prime_accounting(Check::Cancellation);
}

// ---------------------------------------------------------------------------
// The rules of the prime fields

const OUTSIDE_DOMAIN: ErrorKind = ErrorKind::Fault(FaultKind::OutsideDomain);

const DIVISION_BY_ZERO: ErrorKind = ErrorKind::Fault(FaultKind::DivisionByZero);

/// A fresh context with default limits.
fn fresh() -> Context {
    Context::new(Limits::new(), CancelFlag::new())
}

/// A cancelled context with `limits`.
fn cancelled(limits: Limits) -> Context {
    let flag = CancelFlag::new();
    flag.cancel();
    Context::new(limits, flag)
}

/// The kind of `error` and the identifier of the limit that it exceeded.
fn outcome(error: &Error) -> (ErrorKind, Option<LimitId>) {
    (
        error.kind(),
        error.exceeded().map(|limit| limit.id().clone()),
    )
}

/// $a^e \bmod m$ in `u128`, by binary powering, for $m \lt 2^{64}$.
fn power_modulo(a: u128, e: u128, m: u128) -> u128 {
    let (mut result, mut base, mut e) = (1 % m, a % m, e);
    while e != 0 {
        if e & 1 == 1 {
            result = result * base % m;
        }
        base = base * base % m;
        e >>= 1;
    }
    result
}

/// Whether the odd $n \ge 3$ passes the strong probable-prime test to the
/// base $a$, in `u128` arithmetic written here.
fn strong_probable_prime(n: u128, a: u128) -> bool {
    let (mut odd, mut twos) = (n - 1, 0);
    while odd % 2 == 0 {
        odd /= 2;
        twos += 1;
    }
    let mut x = power_modulo(a, odd, n);
    if x == 1 || x == n - 1 {
        return true;
    }
    for _ in 1..twos {
        x = x * x % n;
        if x == n - 1 {
            return true;
        }
    }
    false
}

/// `PrimeField::new(p)` fails with `Fault(OutsideDomain)` before any check
/// or charge: also under no bits and no work in a cancelled context.
fn assert_rejected_at_once(p: u32) {
    for mut context in [
        fresh(),
        cancelled(Limits::new().with_max_integer_bits(0).with_max_work(0)),
    ] {
        let error = PrimeField::new(p, &mut context).unwrap_err();
        assert_eq!(outcome(&error), (OUTSIDE_DOMAIN, None), "{p}");
        assert!(error.span().is_none());
        assert_eq!(context.work_used(), 0, "{p} charges nothing");
    }
}

#[test]
fn a_prime_field_rejects_the_modulus_zero() {
    assert_rejected_at_once(0);
}

#[test]
fn a_prime_field_rejects_the_modulus_one() {
    assert_rejected_at_once(1);
}

#[test]
fn a_prime_field_rejects_the_modulus_four() {
    assert_rejected_at_once(4);
}

// 3215031751 = 151 * 751 * 28351 is a strong pseudoprime to the bases 2,
// 3, 5 and 7; of the bases 2, 7 and 61 of the test, only 61 reveals it, so
// a test to fewer bases would accept it. It is rejected after the charges
// of the test, which are kept, and no field is built.
#[test]
fn a_prime_field_rejects_the_strong_pseudoprime_3215031751() {
    let n: u32 = 3_215_031_751;
    assert_eq!(151 * 751 * 28_351, u64::from(n));
    for base in [2, 3, 5, 7] {
        assert!(strong_probable_prime(u128::from(n), base), "base {base}");
    }
    assert!(!strong_probable_prime(u128::from(n), 61));
    let context = &mut fresh();
    let before = context.retained();
    let error = PrimeField::new(n, context).unwrap_err();
    assert_eq!(outcome(&error), (OUTSIDE_DOMAIN, None));
    assert!(context.work_used() > 0, "the test is charged");
    assert_eq!(context.retained(), before);
}

#[test]
fn a_prime_field_accepts_the_primes_2_3_and_4294967291() {
    // 7 and 61 are bases of the test, which skips a base equal to p: the
    // residue of such a base is 0, whose powers never reach 1 or p - 1.
    for p in [2, 3, 4_294_967_291, 7, 61, 65_537] {
        for base in [2, 7, 61] {
            if p > 2 && u128::from(p) != base {
                assert!(
                    strong_probable_prime(u128::from(p), base),
                    "{p}, base {base}"
                );
            }
        }
        let field = PrimeField::new(p, &mut fresh()).unwrap();
        assert_eq!(field.modulus(), p);
    }
    // The constructor under the accounting checks of the tool: with the
    // budget it needs it builds the field or rejects the composite, with
    // one unit less it fails for `max_work`, and a cancellation at each of
    // its charge points stops it; the context retains nothing more.
    let limits = Limits::new();
    for p in [4_294_967_291, 3_215_031_751] {
        let label = format!("PrimeField::new({p})");
        let run = |c: &mut Context| PrimeField::new(p, c);
        let show = |field: &PrimeField| format!("{field:?}");
        let canonical = |field: &PrimeField| field.modulus() == p;
        let inputs = String::new;
        let run = Run {
            label: &label,
            run: &run,
            show: &show,
            canonical: &canonical,
            inputs: &inputs,
        };
        work_accounting(&limits, &run);
        cancellation(&limits, &run);
    }
}

#[test]
fn a_prime_field_inverts_zero_to_division_by_zero_without_a_charge() {
    for p in PRIMES {
        let c = &mut roomy();
        let field = PrimeField::new(p, c).unwrap();
        let zero = field.zero(c).unwrap();
        let minus_one = field.from_integer(&Integer::from(-1_i64), c).unwrap();
        let dividends = [zero, field.one(c).unwrap(), minus_one];
        assert_eq!(minus_one.value(), p - 1);
        for mut context in [
            Context::new(Limits::new().with_max_integer_bits(1), CancelFlag::new()),
            cancelled(Limits::new()),
        ] {
            let before = context.work_used();
            let error = field.inverse(&zero, &mut context).unwrap_err();
            assert_eq!(outcome(&error), (DIVISION_BY_ZERO, None), "1 / 0 in F_{p}");
            for a in &dividends {
                let error = field.divide(a, &zero, &mut context).unwrap_err();
                assert_eq!(
                    outcome(&error),
                    (DIVISION_BY_ZERO, None),
                    "{} / 0 in F_{p}",
                    a.value()
                );
            }
            assert_eq!(
                context.work_used(),
                before,
                "a zero divisor charges nothing"
            );
        }
    }
}

/// An element operation that builds a residue of at most `bits` bits for
/// `amount` units: under one bit less it fails with `ResourceLimit` naming
/// `max_integer_bits` and charges nothing, with one unit less it fails with
/// `ResourceLimit` naming `max_work`, and with both it charges `amount`.
fn assert_admission(
    what: &str,
    bits: u64,
    amount: u64,
    run: &dyn Fn(&mut Context) -> Result<PrimeResidue>,
) {
    let limits = Limits::new().with_max_integer_bits(bits);
    let narrow = &mut Context::new(limits.with_max_integer_bits(bits - 1), CancelFlag::new());
    let error = run(narrow).unwrap_err();
    let integer_bits = Some(LimitId::Field(LimitField::IntegerBits));
    assert_eq!(
        outcome(&error),
        (ErrorKind::ResourceLimit, integer_bits),
        "{what}"
    );
    assert_eq!(
        narrow.work_used(),
        0,
        "{what}: a rejected bound charges nothing"
    );
    let short = &mut Context::new(limits.with_max_work(amount - 1), CancelFlag::new());
    let error = run(short).unwrap_err();
    let work = Some(LimitId::Field(LimitField::Work));
    assert_eq!(outcome(&error), (ErrorKind::ResourceLimit, work), "{what}");
    let exact = &mut Context::new(limits.with_max_work(amount), CancelFlag::new());
    run(exact).unwrap();
    assert_eq!(exact.work_used(), amount, "{what}");
}

#[test]
fn prime_fields_check_and_charge_new_elements() {
    for p in PRIMES {
        let c = &mut roomy();
        let field = PrimeField::new(p, c).unwrap();
        let bits = u64::from(u32::BITS - p.leading_zeros());
        let a = field.one(c).unwrap();
        let b = field.from_integer(&Integer::from(-1_i64), c).unwrap();
        let minus_one = Integer::from(-1_i64);
        let wide = Integer::from(1_u64 << 40);
        let label = |what: &str| format!("{what} in F_{p}");
        assert_admission(&label("0"), bits, 1, &|c| field.zero(c));
        assert_admission(&label("1"), bits, 1, &|c| field.one(c));
        assert_admission(&label("-1 * 1"), bits, 2, &|c| {
            field.from_integer(&minus_one, c)
        });
        assert_admission(&label("2^40 * 1"), 41, 2, &|c| field.from_integer(&wide, c));
        assert_admission(&label("-a"), bits, 1, &|c| field.negate(&a, c));
        assert_admission(&label("a + b"), bits, 1, &|c| field.add(&a, &b, c));
        assert_admission(&label("a - b"), bits, 1, &|c| field.subtract(&a, &b, c));
        assert_admission(&label("a b"), bits, 1, &|c| field.multiply(&a, &b, c));
        assert_admission(&label("1 / b"), bits, 32, &|c| field.inverse(&b, c));
        assert_admission(&label("a / b"), bits, 32, &|c| field.divide(&a, &b, c));
    }
}

// The inverse of the earlier implementation charged one unit per bit of
// p - 2 in its loop; the kernel now takes no context, and the inverse
// charges 32 units before it, the bits of p - 2 for the largest p.
#[test]
fn inverses_charge_a_fixed_amount_and_nothing_for_zero() {
    let c = &mut roomy();
    let seven = PrimeField::new(7, c).unwrap();
    let three = seven.from_integer(&Integer::from(3_i64), c).unwrap();
    let zero = seven.zero(c).unwrap();
    for work in [32, 33, 100] {
        let context = &mut Context::new(Limits::new().with_max_work(work), CancelFlag::new());
        assert_eq!(seven.inverse(&three, context).unwrap().value(), 5);
        assert_eq!(context.work_used(), 32);
    }
    let context = &mut Context::new(Limits::new().with_max_work(31), CancelFlag::new());
    let error = seven.inverse(&three, context).unwrap_err();
    let work = Some(LimitId::Field(LimitField::Work));
    assert_eq!(outcome(&error), (ErrorKind::ResourceLimit, work));
    assert!(error.span().is_none());
    assert_eq!(context.work_used(), 0);
    for mut context in [
        Context::new(Limits::new().with_max_work(0), CancelFlag::new()),
        cancelled(Limits::new().with_max_work(0)),
    ] {
        let error = seven.inverse(&zero, &mut context).unwrap_err();
        assert_eq!(outcome(&error), (DIVISION_BY_ZERO, None));
        assert!(error.span().is_none());
        assert_eq!(context.work_used(), 0);
    }
    let context = &mut cancelled(Limits::new());
    let error = seven.inverse(&three, context).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Cancelled);
    assert_eq!(context.work_used(), 0);
    let p = 4_294_967_291;
    let large = PrimeField::new(p, c).unwrap();
    for n in [1_i64, 2, -1] {
        let a = large.from_integer(&Integer::from(n), c).unwrap();
        let before = c.work_used();
        let inverse = large.inverse(&a, c).unwrap();
        let product = u128::from(a.value()) * u128::from(inverse.value()) % u128::from(p);
        assert_eq!(product, 1, "1 / {n} in F_{p}");
        assert_eq!(c.work_used() - before, 32);
    }
}

#[test]
fn prime_fields_decide_every_zero_test_without_a_charge() {
    let c = &mut roomy();
    let five = PrimeField::new(5, c).unwrap();
    let seven = PrimeField::new(7, c).unwrap();
    let zero = seven.zero(c).unwrap();
    let six = seven.from_integer(&Integer::from(-1_i64), c).unwrap();
    let context = &mut Context::new(Limits::new().with_max_work(0), CancelFlag::new());
    let answer: ZeroTest<Infallible> = seven.zero_test(&zero, context).unwrap();
    assert_eq!(answer, ZeroTest::Zero);
    assert_eq!(seven.zero_test(&six, context).unwrap(), ZeroTest::Nonzero);
    assert!(seven.same_parent(&seven, context).unwrap());
    assert!(
        seven
            .same_parent(&PrimeField::new(7, c).unwrap(), context)
            .unwrap()
    );
    assert!(!five.same_parent(&seven, context).unwrap());
    assert!(!seven.same_parent(&five, context).unwrap());
    assert_eq!(context.work_used(), 0);
}

// `measure` of a prime field is one node and |r| + 4 bytes for the residue
// r, the cost of the integer r. It takes no context, so it neither charges
// nor fails: the work used after the samples are built does not change.
#[test]
fn prime_fields_measure_their_elements_by_the_storage_formula() {
    let measure: fn(&PrimeField, &PrimeResidue) -> Storage =
        <PrimeField as CoefficientRing>::measure;
    let c = &mut roomy();
    let large = PrimeField::new(4_294_967_291, c).unwrap();
    let seven = PrimeField::new(7, c).unwrap();
    let image = |field: &PrimeField, n: i64, c: &mut Context| {
        field.from_integer(&Integer::from(n), c).unwrap()
    };
    let samples = [
        (large, large.zero(c).unwrap(), Storage::new(1, 4)),
        (large, large.one(c).unwrap(), Storage::new(1, 5)),
        (large, image(&large, 1 << 31, c), Storage::new(1, 32 + 4)),
        (large, image(&large, -1, c), Storage::new(1, 32 + 4)),
        (seven, image(&seven, 10, c), Storage::new(1, 2 + 4)),
        (seven, image(&seven, -1, c), Storage::new(1, 3 + 4)),
    ];
    let used = c.work_used();
    for (field, element, expected) in &samples {
        assert_eq!(measure(field, element), *expected, "{}", element.value());
    }
    assert_eq!(c.work_used(), used);
}

/// The sources of the prime fields, searched for calls of the frames and
/// temporaries of the context.
const PRIME_SOURCES: [&str; 2] = [
    include_str!("../src/coefficient/prime.rs"),
    include_str!("../src/coefficient/prime/traits.rs"),
];

// The element operations open no frame and reserve no temporary: they
// succeed under no frames and under no storage bytes and leave nothing
// retained. `from_integer` is checked under no frames only, since the
// integer division that it calls checks the storage of its result.
#[test]
fn prime_fields_hold_no_frame_or_reservation() {
    let c = &mut roomy();
    let field = PrimeField::new(4_294_967_291, c).unwrap();
    let a = field.from_integer(&Integer::from(3_i64), c).unwrap();
    let b = field.from_integer(&Integer::from(-2_i64), c).unwrap();
    let nothing = Storage::new(0, 0);
    for limits in [
        Limits::new().with_max_frames(0),
        Limits::new().with_max_storage_bytes(0),
    ] {
        let context = &mut Context::new(limits, CancelFlag::new());
        field.zero(context).unwrap();
        field.one(context).unwrap();
        field.negate(&a, context).unwrap();
        field.add(&a, &b, context).unwrap();
        field.subtract(&a, &b, context).unwrap();
        field.multiply(&a, &b, context).unwrap();
        field.inverse(&b, context).unwrap();
        field.divide(&a, &b, context).unwrap();
        field.zero_test(&a, context).unwrap();
        assert_eq!(field.measure(&a), Storage::new(1, 2 + 4));
        assert_eq!(context.retained(), nothing);
        assert_eq!(context.open_frames(), 0);
    }
    let context = &mut Context::new(Limits::new().with_max_frames(0), CancelFlag::new());
    field.from_integer(&Integer::from(-7_i64), context).unwrap();
    assert_eq!(context.retained(), nothing);
    for call in [
        ".reserve(",
        ".release(",
        ".enter_frame(",
        ".set_frame_cost(",
        ".leave_frame(",
    ] {
        for source in PRIME_SOURCES {
            assert!(!source.contains(call), "the prime fields call {call}");
        }
    }
}

// A residue of another field that is below the modulus is taken as a
// residue of the receiver, which the methods assume; one at or above it
// fails with `OutsideDomain` before any check or charge, so that the kernel
// of the difference never goes below zero, and `measure` reads its bits.
#[test]
fn a_residue_beyond_the_modulus_is_outside_the_domain() {
    let c = &mut roomy();
    let five = PrimeField::new(5, c).unwrap();
    let seven = PrimeField::new(7, c).unwrap();
    let three = seven.from_integer(&Integer::from(3_i64), c).unwrap();
    let six = seven.from_integer(&Integer::from(6_i64), c).unwrap();
    let one = five.one(c).unwrap();
    let context = &mut cancelled(Limits::new().with_max_integer_bits(0).with_max_work(0));
    let failures = [
        five.negate(&six, context).map(|_| ()),
        five.add(&one, &six, context).map(|_| ()),
        five.subtract(&one, &six, context).map(|_| ()),
        five.subtract(&six, &one, context).map(|_| ()),
        five.multiply(&six, &one, context).map(|_| ()),
        five.inverse(&six, context).map(|_| ()),
        five.divide(&one, &six, context).map(|_| ()),
        five.divide(&six, &one, context).map(|_| ()),
        five.zero_test(&six, context).map(|_| ()),
    ];
    for (index, result) in failures.into_iter().enumerate() {
        let error = result.unwrap_err();
        assert_eq!(outcome(&error), (OUTSIDE_DOMAIN, None), "operation {index}");
    }
    assert_eq!(context.work_used(), 0);
    assert_eq!(five.measure(&six), Storage::new(1, 3 + 4));
    let sum = five.add(&three, &one, c).unwrap();
    assert_eq!(sum.value(), 4);
}
