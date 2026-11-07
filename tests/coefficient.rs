//! Property tests of the coefficient-field trait.
//!
//! The properties are written once, generically over `K: CoefficientField`,
//! and take a [`Model`] of the field: an independent implementation of its
//! arithmetic in the test code, with the bridge between its values and the
//! elements of the field. They are instantiated with [`Rationals`], whose
//! model is a fraction of two `i128`s with its own GCD; the sampled operands
//! are small enough that no `i128` operation of the model overflows. Each
//! family runs 1,000 cases compared with the model, from a fixed seed, and
//! then large operands, checked by the identities of the trait alone.

#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    clippy::panic,
    reason = "the helpers of the tests unwrap their results and panic on a failed premise, as the tests do"
)]

use std::convert::Infallible;
use std::fmt;

use kalyx::coefficient::{CoefficientField, CoefficientRing, Rationals, ZeroTest};
use kalyx::context::{CancelFlag, Storage, StorageCost};
use kalyx::number::{Integer, Rational};
use kalyx::{Context, ErrorKind, FaultKind, Limits};

/// The cases of each property family that are compared with the model.
const CASES: usize = 1_000;

/// The cases of each family with large operands.
const LARGE_CASES: usize = 50;

// ---------------------------------------------------------------------------
// The generator

/// SplitMix64, a fixed-seed generator written here; the tests use no
/// external generator.
struct SplitMix64(u64);

impl SplitMix64 {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A value in `0..bound`.
    fn below(&mut self, bound: u64) -> u64 {
        self.next() % bound
    }

    /// A value in `low..=high`.
    fn between(&mut self, low: i64, high: i64) -> i64 {
        let span = u64::try_from(high - low).unwrap() + 1;
        low + i64::try_from(self.below(span)).unwrap()
    }
}

// ---------------------------------------------------------------------------
// The model of a field

/// An independent model of the field `K` and the bridge to its elements.
trait Model<K: CoefficientField> {
    /// A value of the model.
    type Value: Clone + PartialEq + fmt::Debug + fmt::Display;

    /// A small value, sometimes zero, one or an integer.
    fn sample(&self, random: &mut SplitMix64) -> Self::Value;
    fn zero(&self) -> Self::Value;
    fn one(&self) -> Self::Value;
    fn add(&self, a: &Self::Value, b: &Self::Value) -> Self::Value;
    fn subtract(&self, a: &Self::Value, b: &Self::Value) -> Self::Value;
    fn multiply(&self, a: &Self::Value, b: &Self::Value) -> Self::Value;
    fn negate(&self, a: &Self::Value) -> Self::Value;
    /// The inverse, or `None` for zero.
    fn inverse(&self, a: &Self::Value) -> Option<Self::Value>;

    /// Integers $n$ and $d \ne 0$ with $n \cdot 1 / d \cdot 1$ equal to
    /// `value` in `K`, both scaled by `scale`; $d \cdot 1$ must be nonzero
    /// in `K`.
    fn fraction(&self, value: &Self::Value, scale: i64) -> (Integer, Integer);

    /// Whether `element` is `value`, judged by the model.
    fn agrees(&self, element: &K::Element, value: &Self::Value) -> bool;

    /// The text of the stored form of `element`, which a canonical
    /// representation makes unique.
    fn representation(&self, element: &K::Element) -> String;

    /// The display text of `element`.
    fn text(&self, element: &K::Element) -> String;
}

/// A rational in the model: an `i128` numerator over a positive `i128`
/// denominator in lowest terms, reduced with the GCD below.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Fraction {
    numerator: i128,
    denominator: i128,
}

fn gcd(mut a: i128, mut b: i128) -> i128 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

impl Fraction {
    fn new(numerator: i128, denominator: i128) -> Self {
        assert_ne!(denominator, 0);
        let sign = if denominator < 0 { -1 } else { 1 };
        let divisor = gcd(numerator, denominator);
        if divisor == 0 {
            return Self {
                numerator: 0,
                denominator: 1,
            };
        }
        Self {
            numerator: sign * numerator / divisor,
            denominator: sign * denominator / divisor,
        }
    }
}

impl fmt::Display for Fraction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.denominator == 1 {
            write!(f, "{}", self.numerator)
        } else {
            write!(f, "{}/{}", self.numerator, self.denominator)
        }
    }
}

/// The model of $\mathbb{Q}$. Sampled numerators and denominators have at most
/// 16 bits, so the values of three-operand properties stay far below $2^{127}$.
struct RationalModel;

impl Model<Rationals> for RationalModel {
    type Value = Fraction;

    fn sample(&self, random: &mut SplitMix64) -> Fraction {
        let limit = 1 << 15;
        match random.below(8) {
            0 => Fraction::new(0, 1),
            1 => Fraction::new(i128::from(random.between(-2, 2)), 1),
            2 => Fraction::new(i128::from(random.between(-limit, limit)), 1),
            3 => Fraction::new(
                i128::from(random.between(-limit, limit)),
                1 << random.below(16),
            ),
            _ => Fraction::new(
                i128::from(random.between(-limit, limit)),
                i128::from(random.between(1, limit)),
            ),
        }
    }

    fn zero(&self) -> Fraction {
        Fraction::new(0, 1)
    }

    fn one(&self) -> Fraction {
        Fraction::new(1, 1)
    }

    fn add(&self, a: &Fraction, b: &Fraction) -> Fraction {
        Fraction::new(
            a.numerator * b.denominator + b.numerator * a.denominator,
            a.denominator * b.denominator,
        )
    }

    fn subtract(&self, a: &Fraction, b: &Fraction) -> Fraction {
        Fraction::new(
            a.numerator * b.denominator - b.numerator * a.denominator,
            a.denominator * b.denominator,
        )
    }

    fn multiply(&self, a: &Fraction, b: &Fraction) -> Fraction {
        Fraction::new(a.numerator * b.numerator, a.denominator * b.denominator)
    }

    fn negate(&self, a: &Fraction) -> Fraction {
        Fraction::new(-a.numerator, a.denominator)
    }

    fn inverse(&self, a: &Fraction) -> Option<Fraction> {
        if a.numerator == 0 {
            None
        } else {
            Some(Fraction::new(a.denominator, a.numerator))
        }
    }

    fn fraction(&self, value: &Fraction, scale: i64) -> (Integer, Integer) {
        let scale = i128::from(scale);
        let part = |x: i128| Integer::from(i64::try_from(x * scale).unwrap());
        (part(value.numerator), part(value.denominator))
    }

    fn agrees(&self, element: &Rational, value: &Fraction) -> bool {
        element.to_string() == value.to_string()
            && element.numerator().to_string() == value.numerator.to_string()
            && element.denominator().to_string() == value.denominator.to_string()
    }

    fn representation(&self, element: &Rational) -> String {
        format!("{element:?}")
    }

    fn text(&self, element: &Rational) -> String {
        element.to_string()
    }
}

// ---------------------------------------------------------------------------
// Helpers over the trait

/// A context whose limits are large enough for every case.
fn context() -> Context {
    Context::new(
        Limits::new()
            .with_max_work(u64::MAX)
            .with_max_integer_bits(1 << 16),
        CancelFlag::new(),
    )
}

/// Whether `a` is zero; an undecided answer fails the test, since every field
/// that the properties run on decides.
fn is_zero<K: CoefficientField>(field: &K, a: &K::Element, context: &mut Context) -> bool {
    match field.zero_test(a, context).unwrap() {
        ZeroTest::Zero => true,
        ZeroTest::Nonzero => false,
        ZeroTest::Undecided(_) => panic!("the zero test did not decide"),
    }
}

/// Whether `a` and `b` are equal in the field: their difference is zero.
fn equal<K: CoefficientField>(
    field: &K,
    a: &K::Element,
    b: &K::Element,
    context: &mut Context,
) -> bool {
    let difference = field.subtract(a, b, context).unwrap();
    is_zero(field, &difference, context)
}

/// The element of `value`, built as $n \cdot 1 / d \cdot 1$.
fn element<K: CoefficientField, M: Model<K>>(
    field: &K,
    model: &M,
    value: &M::Value,
    context: &mut Context,
) -> K::Element {
    let (n, d) = model.fraction(value, 1);
    let n = field.from_integer(&n, context).unwrap();
    let d = field.from_integer(&d, context).unwrap();
    field.divide(&n, &d, context).unwrap()
}

/// A sampled value with its element.
fn sample<K: CoefficientField, M: Model<K>>(
    field: &K,
    model: &M,
    random: &mut SplitMix64,
    context: &mut Context,
) -> (K::Element, M::Value) {
    let value = model.sample(random);
    (element(field, model, &value, context), value)
}

/// A large element: the product of four quotients of 64-bit integer images,
/// built through the trait alone.
fn large<K: CoefficientField>(
    field: &K,
    random: &mut SplitMix64,
    context: &mut Context,
) -> K::Element {
    let mut product = field.one(context).unwrap();
    for _ in 0..4 {
        let n = nonzero_image(field, random, 0, context);
        let d = nonzero_image(field, random, 1, context);
        let quotient = field.divide(&n, &d, context).unwrap();
        product = field.multiply(&product, &quotient, context).unwrap();
    }
    if random.below(2) == 0 {
        field.negate(&product, context).unwrap()
    } else {
        product
    }
}

/// The image of the fresh random integer `random.next() | low_bit`, drawn
/// again while the image is zero, which can happen only in a field of
/// positive characteristic.
fn nonzero_image<K: CoefficientField>(
    field: &K,
    random: &mut SplitMix64,
    low_bit: u64,
    context: &mut Context,
) -> K::Element {
    loop {
        let image = field
            .from_integer(&Integer::from(random.next() | low_bit), context)
            .unwrap();
        if !is_zero(field, &image, context) {
            return image;
        }
    }
}

/// The error of `result`, which must have failed.
fn error_of<T>(result: kalyx::Result<T>) -> kalyx::Error {
    match result {
        Ok(_) => panic!("the operation succeeded"),
        Err(error) => error,
    }
}

fn assert_agrees<K: CoefficientField, M: Model<K>>(
    model: &M,
    element: &K::Element,
    value: &M::Value,
    what: &str,
) {
    assert!(
        model.agrees(element, value),
        "{what}: {} is not {value}",
        model.text(element)
    );
}

// ---------------------------------------------------------------------------
// The properties

/// $(a + b) + c = a + (b + c)$ and $(a b) c = a (b c)$.
fn associativity<K: CoefficientField, M: Model<K>>(field: &K, model: &M, seed: u64) {
    let mut random = SplitMix64(seed);
    let mut context = context();
    let c = &mut context;
    for _ in 0..CASES {
        let (a, av) = sample(field, model, &mut random, c);
        let (b, bv) = sample(field, model, &mut random, c);
        let (d, dv) = sample(field, model, &mut random, c);
        let left = field.add(&field.add(&a, &b, c).unwrap(), &d, c).unwrap();
        let right = field.add(&a, &field.add(&b, &d, c).unwrap(), c).unwrap();
        let expected = model.add(&model.add(&av, &bv), &dv);
        assert_agrees(model, &left, &expected, "(a + b) + c");
        assert_agrees(model, &right, &expected, "a + (b + c)");
        let left = field
            .multiply(&field.multiply(&a, &b, c).unwrap(), &d, c)
            .unwrap();
        let right = field
            .multiply(&a, &field.multiply(&b, &d, c).unwrap(), c)
            .unwrap();
        let expected = model.multiply(&model.multiply(&av, &bv), &dv);
        assert_agrees(model, &left, &expected, "(a b) c");
        assert_agrees(model, &right, &expected, "a (b c)");
    }
    for _ in 0..LARGE_CASES {
        let (a, b, d) = (
            large(field, &mut random, c),
            large(field, &mut random, c),
            large(field, &mut random, c),
        );
        let left = field.add(&field.add(&a, &b, c).unwrap(), &d, c).unwrap();
        let right = field.add(&a, &field.add(&b, &d, c).unwrap(), c).unwrap();
        assert!(equal(field, &left, &right, c));
        let left = field
            .multiply(&field.multiply(&a, &b, c).unwrap(), &d, c)
            .unwrap();
        let right = field
            .multiply(&a, &field.multiply(&b, &d, c).unwrap(), c)
            .unwrap();
        assert!(equal(field, &left, &right, c));
        assert_eq!(model.representation(&left), model.representation(&right));
    }
}

/// $a + b = b + a$ and $a b = b a$.
fn commutativity<K: CoefficientField, M: Model<K>>(field: &K, model: &M, seed: u64) {
    let mut random = SplitMix64(seed);
    let mut context = context();
    let c = &mut context;
    for _ in 0..CASES {
        let (a, av) = sample(field, model, &mut random, c);
        let (b, bv) = sample(field, model, &mut random, c);
        let expected = model.add(&av, &bv);
        assert_agrees(model, &field.add(&a, &b, c).unwrap(), &expected, "a + b");
        assert_agrees(model, &field.add(&b, &a, c).unwrap(), &expected, "b + a");
        let expected = model.multiply(&av, &bv);
        assert_agrees(model, &field.multiply(&a, &b, c).unwrap(), &expected, "a b");
        assert_agrees(model, &field.multiply(&b, &a, c).unwrap(), &expected, "b a");
        let expected = model.subtract(&av, &bv);
        assert_agrees(
            model,
            &field.subtract(&a, &b, c).unwrap(),
            &expected,
            "a - b",
        );
    }
    for _ in 0..LARGE_CASES {
        let (a, b) = (large(field, &mut random, c), large(field, &mut random, c));
        let left = field.add(&a, &b, c).unwrap();
        let right = field.add(&b, &a, c).unwrap();
        assert_eq!(model.representation(&left), model.representation(&right));
        let left = field.multiply(&a, &b, c).unwrap();
        let right = field.multiply(&b, &a, c).unwrap();
        assert_eq!(model.representation(&left), model.representation(&right));
    }
}

/// $a (b + c) = a b + a c$ and $(a + b) c = a c + b c$.
fn distributivity<K: CoefficientField, M: Model<K>>(field: &K, model: &M, seed: u64) {
    let mut random = SplitMix64(seed);
    let mut context = context();
    let c = &mut context;
    for _ in 0..CASES {
        let (a, av) = sample(field, model, &mut random, c);
        let (b, bv) = sample(field, model, &mut random, c);
        let (d, dv) = sample(field, model, &mut random, c);
        let left = field
            .multiply(&a, &field.add(&b, &d, c).unwrap(), c)
            .unwrap();
        let ab = field.multiply(&a, &b, c).unwrap();
        let ad = field.multiply(&a, &d, c).unwrap();
        let right = field.add(&ab, &ad, c).unwrap();
        let expected = model.multiply(&av, &model.add(&bv, &dv));
        assert_agrees(model, &left, &expected, "a (b + c)");
        assert_agrees(model, &right, &expected, "a b + a c");
        let left = field
            .multiply(&field.subtract(&a, &b, c).unwrap(), &d, c)
            .unwrap();
        let ad = field.multiply(&a, &d, c).unwrap();
        let bd = field.multiply(&b, &d, c).unwrap();
        let right = field.subtract(&ad, &bd, c).unwrap();
        let expected = model.multiply(&model.subtract(&av, &bv), &dv);
        assert_agrees(model, &left, &expected, "(a - b) c");
        assert_agrees(model, &right, &expected, "a c - b c");
    }
    for _ in 0..LARGE_CASES {
        let (a, b, d) = (
            large(field, &mut random, c),
            large(field, &mut random, c),
            large(field, &mut random, c),
        );
        let left = field
            .multiply(&a, &field.add(&b, &d, c).unwrap(), c)
            .unwrap();
        let ab = field.multiply(&a, &b, c).unwrap();
        let ad = field.multiply(&a, &d, c).unwrap();
        let right = field.add(&ab, &ad, c).unwrap();
        assert!(equal(field, &left, &right, c));
        assert_eq!(model.representation(&left), model.representation(&right));
    }
}

/// $a + (-a) = 0$, $-(-a) = a$, $a a^{-1} = 1$ and $a / b = a b^{-1}$ for
/// $b \ne 0$; the inverse of zero and a quotient by zero fail with
/// `DivisionByZero` before any charge.
fn inverses<K: CoefficientField, M: Model<K>>(field: &K, model: &M, seed: u64) {
    let mut random = SplitMix64(seed);
    let mut context = context();
    let c = &mut context;
    let mut zeros = 0;
    for _ in 0..CASES {
        let (a, av) = sample(field, model, &mut random, c);
        let (b, bv) = sample(field, model, &mut random, c);
        let negated = field.negate(&a, c).unwrap();
        assert_agrees(model, &negated, &model.negate(&av), "-a");
        let sum = field.add(&a, &negated, c).unwrap();
        assert!(is_zero(field, &sum, c));
        assert_agrees(model, &sum, &model.zero(), "a + (-a)");
        assert_agrees(model, &field.negate(&negated, c).unwrap(), &av, "-(-a)");
        assert_eq!(is_zero(field, &a, c), av == model.zero());
        match model.inverse(&av) {
            Some(inverse) => {
                let actual = field.inverse(&a, c).unwrap();
                assert_agrees(model, &actual, &inverse, "1 / a");
                let one = field.multiply(&a, &actual, c).unwrap();
                assert_agrees(model, &one, &model.one(), "a (1 / a)");
            }
            None => {
                zeros += 1;
                let before = c.work_used();
                let error = error_of(field.inverse(&a, c));
                assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::DivisionByZero));
                let error = error_of(field.divide(&b, &a, c));
                assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::DivisionByZero));
                assert_eq!(c.work_used(), before);
            }
        }
        if let Some(inverse) = model.inverse(&bv) {
            let quotient = field.divide(&a, &b, c).unwrap();
            assert_agrees(model, &quotient, &model.multiply(&av, &inverse), "a / b");
            let product = field
                .multiply(&a, &field.inverse(&b, c).unwrap(), c)
                .unwrap();
            assert_eq!(
                model.representation(&quotient),
                model.representation(&product)
            );
        }
    }
    assert!(zeros > 0, "the sample holds zeros");
    let zero = field.zero(c).unwrap();
    let one = field.one(c).unwrap();
    for _ in 0..LARGE_CASES {
        let a = large(field, &mut random, c);
        let inverse = field.inverse(&a, c).unwrap();
        let product = field.multiply(&a, &inverse, c).unwrap();
        assert!(equal(field, &product, &one, c));
        assert_eq!(model.representation(&product), model.representation(&one));
        let negated = field.negate(&a, c).unwrap();
        let sum = field.add(&a, &negated, c).unwrap();
        assert_eq!(model.representation(&sum), model.representation(&zero));
        assert!(field.divide(&a, &zero, c).is_err());
    }
}

/// Equal values built in different ways have the same stored form and the
/// same display text: $(n k) / (d k)$, $n \cdot d^{-1}$, $-((-n k) / (d k))$
/// and $(x + w) - w$.
fn canonical_uniqueness<K: CoefficientField, M: Model<K>>(field: &K, model: &M, seed: u64) {
    let mut random = SplitMix64(seed);
    let mut context = context();
    let c = &mut context;
    for _ in 0..CASES {
        let value = model.sample(&mut random);
        // A scale whose image is nonzero, which only a field of positive
        // characteristic can fail to give.
        let scale = loop {
            let k = random.between(1, 1 << 15);
            let image = field.from_integer(&Integer::from(k), c).unwrap();
            if !is_zero(field, &image, c) {
                break k;
            }
        };
        let (n, d) = model.fraction(&value, scale);
        let n_image = field.from_integer(&n, c).unwrap();
        let d_image = field.from_integer(&d, c).unwrap();
        let scaled = field.divide(&n_image, &d_image, c).unwrap();
        let (n, d) = model.fraction(&value, 1);
        let n_image = field.from_integer(&n, c).unwrap();
        let d_image = field.from_integer(&d, c).unwrap();
        let inverted = field
            .multiply(&n_image, &field.inverse(&d_image, c).unwrap(), c)
            .unwrap();
        let (n, d) = model.fraction(&model.negate(&value), scale);
        let n_image = field.from_integer(&n, c).unwrap();
        let d_image = field.from_integer(&d, c).unwrap();
        let negated = field
            .negate(&field.divide(&n_image, &d_image, c).unwrap(), c)
            .unwrap();
        let (w, _) = sample(field, model, &mut random, c);
        let shifted = field
            .subtract(&field.add(&scaled, &w, c).unwrap(), &w, c)
            .unwrap();
        for other in [&inverted, &negated, &shifted] {
            assert_eq!(model.representation(&scaled), model.representation(other));
            assert_eq!(model.text(&scaled), model.text(other));
            assert!(equal(field, &scaled, other, c));
        }
        assert_agrees(model, &scaled, &value, "(n k) / (d k)");
    }
    for _ in 0..LARGE_CASES {
        let (a, b) = (large(field, &mut random, c), large(field, &mut random, c));
        let product = field.multiply(&a, &b, c).unwrap();
        let back = field.divide(&product, &b, c).unwrap();
        assert_eq!(model.representation(&back), model.representation(&a));
        assert_eq!(model.text(&back), model.text(&a));
    }
}

// ---------------------------------------------------------------------------
// The field of rationals

#[test]
fn rationals_are_associative() {
    associativity(&Rationals, &RationalModel, 0x0A55_0C1A);
}

#[test]
fn rationals_are_commutative() {
    commutativity(&Rationals, &RationalModel, 0xC033_07A7);
}

#[test]
fn rationals_are_distributive() {
    distributivity(&Rationals, &RationalModel, 0xD157_7B07);
}

#[test]
fn rationals_have_inverses_and_zero_has_none() {
    inverses(&Rationals, &RationalModel, 0x1A7E_25E5);
}

#[test]
fn rationals_have_unique_canonical_forms() {
    canonical_uniqueness(&Rationals, &RationalModel, 0xCA10_0CA1);
}

#[test]
fn the_model_reduces_like_a_field_of_fractions() {
    assert_eq!(Fraction::new(6, -4), Fraction::new(-3, 2));
    assert_eq!(Fraction::new(0, -7).to_string(), "0");
    assert_eq!(Fraction::new(-10, 5).to_string(), "-2");
    assert_eq!(gcd(-12, 18), 6);
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
