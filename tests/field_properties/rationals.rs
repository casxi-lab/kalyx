//! The field $\mathbb{Q}$ under the property checks: its adapter, its
//! independent model and the generated and fixed inputs of the checks.
//!
//! The operations of the checks are those of `Rationals` through
//! [`Library`]; the adapter only reads stored forms and builds inputs. The
//! model is a reduced fraction of two `i128`s with its own GCD, which serves
//! the small operands; large operands are checked by identities alone. The
//! inputs are built with the constructors and the arithmetic of `Rational`,
//! which `Rationals` delegates to, not through the layers under test, and
//! serve only as inputs: integers wider than 64 bits come from
//! `Sequence::integer_bits`, and denominators $2^k$ and $3 \cdot 2^k$ from
//! `Rational::power` and `Rational::multiply`.

use std::fmt;

use kalyx::coefficient::Rationals;
use kalyx::number::{Integer, Rational};
use kalyx::polynomial::{Polynomial, PolynomialRing};

use super::{FieldModel, Inspect, Library, Model, Modelled, Polynomials, polynomials, roomy};
use crate::support::Sequence;

/// The variable of the generated polynomials.
pub const VARIABLE: &str = "x";

/// The images $n \cdot 1$ of the integer checks.
pub const INTEGERS: [i64; 9] = [0, 1, -1, 2, -7, 1 << 40, -(1 << 53), i64::MAX, i64::MIN];

/// The adapter of $\mathbb{Q}$.
pub struct RationalAdapter {
    ring: Library<Rationals>,
}

/// The adapter of $\mathbb{Q}$, over `Rationals`.
pub const RATIONALS: RationalAdapter = RationalAdapter {
    ring: Library(Rationals),
};

/// A rational in the model: an `i128` numerator over a positive `i128`
/// denominator in lowest terms, reduced with the GCD below.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Fraction {
    pub numerator: i128,
    pub denominator: i128,
}

/// The greatest common divisor of $\lvert a \rvert$ and $\lvert b \rvert$.
pub fn gcd(mut a: i128, mut b: i128) -> i128 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

impl Fraction {
    pub fn new(numerator: i128, denominator: i128) -> Self {
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

/// The model of $\mathbb{Q}$. Sampled numerators and denominators have at
/// most 16 bits, so the values of three-operand properties stay far below
/// $2^{127}$; its arithmetic panics on an overflow.
pub struct RationalModel;

impl Model for RationalModel {
    type Value = Fraction;

    fn label(&self) -> String {
        "reduced i128 fractions".into()
    }

    fn zero(&self) -> Fraction {
        Fraction::new(0, 1)
    }

    fn one(&self) -> Fraction {
        Fraction::new(1, 1)
    }

    fn integer(&self, n: i128) -> Fraction {
        Fraction::new(n, 1)
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
}

impl FieldModel for RationalModel {
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
}

/// The `i128` of an integer of at most 126 bits, read from its decimal text.
fn word(n: &Integer) -> Option<i128> {
    if n.bits() > 126 {
        return None;
    }
    Some(n.to_string().parse().unwrap())
}

/// Whether a stored rational is canonical: its denominator is positive, and
/// when both parts have at most 126 bits they are coprime by the GCD of the
/// model. A longer rational is only checked for its sign: `Rational` has no
/// unchecked constructor, and its reduction is checked by the identities of
/// the large operands.
pub fn canonical(a: &Rational) -> bool {
    if !a.denominator().is_positive() {
        return false;
    }
    match (word(a.numerator()), word(a.denominator())) {
        (Some(n), Some(d)) => gcd(n, d) == 1,
        _ => true,
    }
}

impl Inspect for RationalAdapter {
    type Ring = Library<Rationals>;

    fn ring(&self) -> &Library<Rationals> {
        &self.ring
    }

    fn label(&self) -> String {
        "the rationals".into()
    }

    fn characteristic(&self) -> u64 {
        0
    }

    fn representation(&self, a: &Rational) -> String {
        format!("{a:?}")
    }

    fn canonical(&self, a: &Rational) -> bool {
        canonical(a)
    }

    fn stored_zero(&self, a: &Rational) -> bool {
        a.numerator().is_zero()
    }
}

/// The integer image of a 64-bit value with a set low bit, drawn again
/// while it is zero, as the large operands of the families draw it.
fn nonzero_draw(random: &mut Sequence, low_bit: u64) -> Integer {
    loop {
        let n = random.next() | low_bit;
        if n != 0 {
            return Integer::from(n);
        }
    }
}

impl Modelled for RationalAdapter {
    type Model = RationalModel;

    fn model(&self) -> &RationalModel {
        &RationalModel
    }

    fn value(&self, a: &Rational) -> Fraction {
        let numerator = word(a.numerator()).expect("a small numerator");
        let denominator = word(a.denominator()).expect("a small denominator");
        Fraction::new(numerator, denominator)
    }

    fn element(&self, value: &Fraction) -> Rational {
        let parts = (
            super::integer_of(value.numerator),
            super::integer_of(value.denominator),
        );
        super::ok("n / d", Rational::new(parts.0, parts.1, &mut roomy()))
    }

    fn agrees(&self, a: &Rational, value: &Fraction) -> bool {
        a.to_string() == value.to_string()
            && a.numerator().to_string() == value.numerator.to_string()
            && a.denominator().to_string() == value.denominator.to_string()
    }

    fn text(&self, a: &Rational) -> String {
        a.to_string()
    }

    fn sample(&self, random: &mut Sequence) -> Fraction {
        let limit = 1 << 15;
        match random.index(8) {
            0 => Fraction::new(0, 1),
            1 => Fraction::new(i128::from(random.next_in(-2, 2)), 1),
            2 => Fraction::new(i128::from(random.next_in(-limit, limit)), 1),
            3 => Fraction::new(
                i128::from(random.next_in(-limit, limit)),
                1 << random.index(16),
            ),
            _ => Fraction::new(
                i128::from(random.next_in(-limit, limit)),
                i128::from(random.next_in(1, limit)),
            ),
        }
    }

    /// The product of four quotients of 64-bit integers, negated half the
    /// time: about 256 bits.
    fn large(&self, random: &mut Sequence) -> Rational {
        let context = &mut roomy();
        let mut product = Rational::from(1_i64);
        for _ in 0..4 {
            let n = nonzero_draw(random, 0);
            let d = nonzero_draw(random, 1);
            let quotient = super::ok("n / d", Rational::new(n, d, context));
            product = super::ok("a b", product.multiply(&quotient, context));
        }
        if random.index(2) == 0 {
            super::ok("-a", product.negate(context))
        } else {
            product
        }
    }
}

// ---------------------------------------------------------------------------
// Inputs

/// The rational `n / d`.
pub fn q(n: i64, d: i64) -> Rational {
    super::ok(
        "n / d",
        Rational::new(Integer::from(n), Integer::from(d), &mut roomy()),
    )
}

/// The integer $2^k$, for a negative $k$ the rational $2^k$, by
/// `Rational::power`.
fn power_of_two(k: i64) -> Rational {
    super::ok("2^k", Rational::from(2_i64).power(k, &mut roomy()))
}

/// The rational $n / d$ of two integers.
fn quotient(n: Integer, d: Integer) -> Rational {
    super::ok("n / d", Rational::new(n, d, &mut roomy()))
}

/// The rationals `n / d` of the given pairs.
fn fixed(values: &[(i64, i64)]) -> Vec<Rational> {
    values.iter().map(|&(n, d)| q(n, d)).collect()
}

/// `value` or its negation, by a drawn sign.
fn signed(sequence: &mut Sequence, value: Integer) -> Integer {
    if sequence.next_in(0, 1) == 0 {
        value
    } else {
        let negated = super::ok("-n", Rational::from(value).negate(&mut roomy()));
        negated.numerator().clone()
    }
}

/// A positive integer of a drawn bit length in `1..=bits`, with its top bit
/// set.
fn positive(sequence: &mut Sequence, bits: i64) -> Integer {
    let bits = u64::try_from(sequence.next_in(1, bits)).unwrap();
    sequence.integer_bits(bits, true)
}

/// A rational of one of eight kinds, selected by `kind`: small integers,
/// integers of up to 200 bits, dyadic fractions with exponents around the
/// word sizes, small fractions, fractions of terms of up to 120 bits,
/// fractions with an even denominator that is not a power of two, unit
/// fractions and a fixed set of tiny values.
fn rational(sequence: &mut Sequence, kind: usize) -> Rational {
    match kind % 8 {
        0 => Rational::from(sequence.next_in(-1000, 1000)),
        1 => {
            let value = positive(sequence, 200);
            Rational::from(signed(sequence, value))
        }
        2 => {
            let exponent = *sequence.pick(&[1_i64, 2, 7, 31, 63, 64, 65, 130]);
            let numerator = positive(sequence, 80);
            let numerator = signed(sequence, numerator);
            quotient(numerator, power_of_two(exponent).numerator().clone())
        }
        3 => q(
            sequence.next_in(-(1 << 20), 1 << 20),
            sequence.next_in(1, 1 << 20),
        ),
        4 => {
            let numerator = positive(sequence, 120);
            let numerator = signed(sequence, numerator);
            quotient(numerator, positive(sequence, 120))
        }
        5 => {
            let exponent = sequence.next_in(1, 70);
            let numerator = Integer::from(sequence.next_in(-(1 << 30), 1 << 30));
            let denominator = super::ok(
                "3 * 2^k",
                Rational::from(3_i64).multiply(&power_of_two(exponent), &mut roomy()),
            );
            quotient(numerator, denominator.numerator().clone())
        }
        6 => {
            let denominator = positive(sequence, 64);
            quotient(signed(sequence, Integer::from(1_i64)), denominator)
        }
        _ => {
            let &(n, d) = sequence.pick(&[
                (0, 1),
                (1, 1),
                (-1, 1),
                (1, 2),
                (-1, 2),
                (2, 1),
                (-2, 1),
                (1, 3),
            ]);
            q(n, d)
        }
    }
}

/// Ten fixed values, $2^{64}$, $2^{-64}$ and $-2^{63}$ among them, followed
/// by `count` generated rationals of every kind.
pub fn rationals(sequence: &mut Sequence, count: usize) -> Vec<Rational> {
    let mut values = fixed(&[(0, 1), (1, 1), (-1, 1), (2, 1), (1, 2), (-3, 4), (7, 3)]);
    values.push(power_of_two(64));
    values.push(power_of_two(-64));
    values.push(Rational::from(i64::MIN));
    values.extend((0..count).map(|kind| rational(sequence, kind)));
    values
}

/// Small rationals for the model: five fixed values, then `count` with
/// numerators and denominators of absolute value at most $2^{24}$.
pub fn small_rationals(sequence: &mut Sequence, count: usize) -> Vec<Rational> {
    let mut values = fixed(&[(0, 1), (1, 1), (-1, 1), (1, 2), (-3, 4)]);
    for index in 0..count {
        let numerator = sequence.next_in(-(1 << 24), 1 << 24);
        let denominator = match index % 3 {
            0 => 1,
            1 => 1 << sequence.next_in(1, 23),
            _ => sequence.next_in(1, 1 << 24),
        };
        values.push(q(numerator, denominator));
    }
    values
}

/// Coefficients for generated polynomials: small integers, small fractions,
/// dyadic fractions with a denominator of at most $2^{20}$, and zero.
pub fn coefficient(sequence: &mut Sequence) -> Rational {
    match sequence.next_in(0, 7) {
        0 => Rational::from(0_i64),
        1..=3 => Rational::from(sequence.next_in(-9, 9)),
        4 | 5 => q(sequence.next_in(-9, 9), sequence.next_in(1, 9)),
        _ => {
            let numerator = Integer::from(sequence.next_in(-99, 99));
            let exponent = sequence.next_in(1, 20);
            quotient(numerator, power_of_two(exponent).numerator().clone())
        }
    }
}

/// The ring $\mathbb{Q}\[x\]$ of the checks.
pub fn polynomial_ring() -> PolynomialRing<Rationals> {
    super::ok(
        "Q[x]",
        PolynomialRing::new(Rationals, VARIABLE, &mut roomy()),
    )
}

/// The zero polynomial and `count` generated polynomials of degree at most
/// eight.
pub fn polynomial_inputs(
    ring: &PolynomialRing<Rationals>,
    sequence: &mut Sequence,
    count: usize,
) -> Vec<Polynomial> {
    let view = Polynomials {
        ring,
        adapter: &RATIONALS,
    };
    polynomials(&view, sequence, count, 8, &mut coefficient)
}

/// The element pairs of the accounting checks: fractions, integers, a
/// dyadic fraction, $2^{90}/7$ and a zero divisor.
pub fn accounting_elements() -> Vec<(Rational, Rational)> {
    let wide = super::ok(
        "2^90 / 7",
        power_of_two(90).divide(&Rational::from(7_i64), &mut roomy()),
    );
    let small = super::ok(
        "3 / 2^20",
        Rational::from(3_i64).multiply(&power_of_two(-20), &mut roomy()),
    );
    vec![
        (q(3, 4), q(-5, 6)),
        (q(7, 1), q(-2, 1)),
        (q(5, 8), small),
        (wide, q(11, 13)),
        (q(1, 2), Rational::from(0_i64)),
    ]
}

/// The polynomial pairs of the accounting checks: $1/2 + x^2$ and $-3 + x$,
/// $1/3 - 2/5 x + 3/2 x^3$ and $1 + 2 x^2$, $x - 1/7 x^4$ and $0$, and $0$
/// and $5$.
pub fn accounting_polynomials(ring: &PolynomialRing<Rationals>) -> Vec<(Polynomial, Polynomial)> {
    let view = Polynomials {
        ring,
        adapter: &RATIONALS,
    };
    let context = &mut roomy();
    let mut p = |terms: &[(u64, Rational)]| view.polynomial(terms, context);
    vec![
        (
            p(&[(0, q(1, 2)), (2, q(1, 1))]),
            p(&[(0, q(-3, 1)), (1, q(1, 1))]),
        ),
        (
            p(&[(0, q(1, 3)), (1, q(-2, 5)), (3, q(3, 2))]),
            p(&[(0, q(1, 1)), (2, q(2, 1))]),
        ),
        (p(&[(1, q(1, 1)), (4, q(-1, 7))]), p(&[])),
        (p(&[]), p(&[(0, q(5, 1))])),
    ]
}
