//! The prime fields $\mathbb F_p$ under the property checks: the adapter of
//! a prime field, its independent model and the generated and fixed inputs
//! of the checks.
//!
//! The operations of the checks are those of `PrimeField` through
//! [`Library`]; the adapter reads the residue of an element with
//! `PrimeResidue::value` and the modulus with `PrimeField::modulus`. The
//! model is the residues modulo $p$ as `u64`, with sums, differences and
//! products in `u128` and the inverse by the extended Euclidean algorithm in
//! `i128`, which shares no step with the field's inverse, a power by
//! Fermat's little theorem.
//!
//! A residue has no public constructor: an element is built only by an
//! operation of its field. The adapter therefore builds the element of a
//! model value, its large elements and the coefficients of the generated
//! polynomials through `from_integer`, one of the operations under test,
//! where the adapter of $\mathbb{Q}$ builds its inputs with the arithmetic
//! of `Rational`, not through the layers under test. Every element that the
//! adapter builds is checked against the value that it was built from, and
//! `from_integer` is checked against the model on its own: the integer
//! images of the comparison with the model, the homomorphism from the
//! integers and its parallel paths, and the characteristic.

use kalyx::coefficient::{PrimeField, PrimeResidue};
use kalyx::number::Integer;
use kalyx::polynomial::{Polynomial, PolynomialRing};

use super::{
    FieldModel, Inspect, Library, Model, Modelled, Polynomials, RingLayer, ok, polynomials, roomy,
};
use crate::support::Sequence;

/// The variable of the generated polynomials.
pub const VARIABLE: &str = "x";

/// The primes of the checks: 2, 3 and 7, whose residues the checks take
/// exhaustively, the prime $2^{16} + 1$ and the largest prime below
/// $2^{32}$.
pub const PRIMES: [u32; 5] = [2, 3, 7, 65_537, 4_294_967_291];

/// The integers whose images the checks of every prime take, those of the
/// checks of the prime fields of the earlier implementation; [`integers`]
/// adds $p$ and $-p$.
pub const INTEGERS: [i64; 10] = [
    0,
    1,
    -1,
    7,
    -65_521,
    4_294_967_291,
    4_294_967_292,
    -12_345_678_901_234,
    i64::MAX,
    i64::MIN,
];

/// The adapter of a prime field, with its model.
pub struct PrimeAdapter {
    ring: Library<PrimeField>,
    model: Residues,
}

impl PrimeAdapter {
    /// The adapter of $\mathbb F_p$, whose field is built by
    /// `PrimeField::new`.
    pub fn new(p: u32) -> Self {
        let field = ok("F_p", PrimeField::new(p, &mut roomy()));
        assert_eq!(field.modulus(), p, "the modulus of F_{p}");
        Self {
            ring: Library(field),
            model: Residues { p: u64::from(p) },
        }
    }

    /// The field.
    pub const fn field(&self) -> &PrimeField {
        &self.ring.0
    }

    /// The modulus $p$.
    pub fn modulus(&self) -> u64 {
        u64::from(self.ring.0.modulus())
    }
}

/// The residues modulo $p$ in the model.
pub struct Residues {
    p: u64,
}

impl Residues {
    /// The `u64` of a value below $p$ that `u128` arithmetic computed.
    fn word(value: u128) -> u64 {
        u64::try_from(value).unwrap()
    }
}

impl Model for Residues {
    type Value = u64;

    fn label(&self) -> String {
        format!("u64 residues modulo {}", self.p)
    }

    fn zero(&self) -> u64 {
        0
    }

    fn one(&self) -> u64 {
        1
    }

    fn integer(&self, n: i128) -> u64 {
        u64::try_from(n.rem_euclid(i128::from(self.p))).unwrap()
    }

    fn add(&self, a: &u64, b: &u64) -> u64 {
        Self::word((u128::from(*a) + u128::from(*b)) % u128::from(self.p))
    }

    fn subtract(&self, a: &u64, b: &u64) -> u64 {
        let p = u128::from(self.p);
        Self::word((u128::from(*a) + p - u128::from(*b)) % p)
    }

    fn multiply(&self, a: &u64, b: &u64) -> u64 {
        Self::word(u128::from(*a) * u128::from(*b) % u128::from(self.p))
    }

    fn negate(&self, a: &u64) -> u64 {
        (self.p - a) % self.p
    }
}

impl FieldModel for Residues {
    /// The inverse by the extended Euclidean algorithm on $p$ and $a$.
    fn inverse(&self, a: &u64) -> Option<u64> {
        if *a == 0 {
            return None;
        }
        let (mut r, mut next_r) = (i128::from(self.p), i128::from(*a));
        let (mut t, mut next_t) = (0_i128, 1_i128);
        while next_r != 0 {
            let q = r / next_r;
            (r, next_r) = (next_r, r - q * next_r);
            (t, next_t) = (next_t, t - q * next_t);
        }
        assert_eq!(r, 1, "{a} is not invertible modulo {}", self.p);
        Some(self.integer(t))
    }

    /// $(v k, k)$ for the residue $v$ and the scale $k \ge 1$.
    fn fraction(&self, value: &u64, scale: i64) -> (Integer, Integer) {
        let scale = u64::try_from(scale).unwrap();
        (Integer::from(value * scale), Integer::from(scale))
    }
}

impl Inspect for PrimeAdapter {
    type Ring = Library<PrimeField>;

    fn ring(&self) -> &Library<PrimeField> {
        &self.ring
    }

    fn label(&self) -> String {
        format!("F_{}", self.modulus())
    }

    fn characteristic(&self) -> u64 {
        self.modulus()
    }

    fn representation(&self, a: &PrimeResidue) -> String {
        format!("{a:?}")
    }

    fn canonical(&self, a: &PrimeResidue) -> bool {
        u64::from(a.value()) < self.modulus()
    }

    fn stored_zero(&self, a: &PrimeResidue) -> bool {
        a.value() == 0
    }
}

impl Modelled for PrimeAdapter {
    type Model = Residues;

    fn model(&self) -> &Residues {
        &self.model
    }

    fn value(&self, a: &PrimeResidue) -> u64 {
        u64::from(a.value())
    }

    /// The element of the residue `value` below $p$, built by
    /// `from_integer` and checked to hold `value`.
    fn element(&self, value: &u64) -> PrimeResidue {
        let element = ok(
            "n * 1",
            self.ring.from_integer(&Integer::from(*value), &mut roomy()),
        );
        assert_eq!(
            u64::from(element.value()),
            *value,
            "{}: the element of {value}",
            self.label()
        );
        element
    }

    fn agrees(&self, a: &PrimeResidue, value: &u64) -> bool {
        u64::from(a.value()) == *value
    }

    fn text(&self, a: &PrimeResidue) -> String {
        a.value().to_string()
    }

    /// Zero, one, $p - 1$, a residue below 17 or any residue.
    fn sample(&self, random: &mut Sequence) -> u64 {
        let p = self.modulus();
        match random.index(8) {
            0 => 0,
            1 => 1,
            2 => p - 1,
            3 => draw(random, p.min(17)),
            _ => draw(random, p),
        }
    }

    /// A residue in $[p - 50, p)$, or any residue for $p \le 50$, the
    /// residues whose sums and products are largest before their reduction.
    fn large(&self, random: &mut Sequence) -> PrimeResidue {
        let p = self.modulus();
        let low = p.saturating_sub(50);
        self.element(&(low + draw(random, p - low)))
    }
}

/// A value below `bound`, which must be positive.
fn draw(random: &mut Sequence, bound: u64) -> u64 {
    u64::try_from(random.next_in(0, i64::try_from(bound - 1).unwrap())).unwrap()
}

// ---------------------------------------------------------------------------
// Inputs

/// The images $n \cdot 1$ of the integer checks of $\mathbb F_p$: the
/// [`INTEGERS`], $p$ and $-p$.
pub fn integers(p: u64) -> Vec<i64> {
    let p = i64::try_from(p).unwrap();
    let mut values = INTEGERS.to_vec();
    values.extend([p, -p]);
    values
}

/// Every residue modulo a prime $p \le 7$; for a larger $p$ the first
/// `fixed` of the residues 0, 1, 2, $p - 2$, $p - 1$, $(p - 1) / 2$ and
/// $p / 2 + 1$, followed by `count` drawn residues.
pub fn residues(p: u64, fixed: usize, count: usize, sequence: &mut Sequence) -> Vec<u64> {
    if p <= 7 {
        return (0..p).collect();
    }
    let mut values: Vec<u64> = [0, 1, 2, p - 2, p - 1, (p - 1) / 2, p / 2 + 1][..fixed].to_vec();
    values.extend((0..count).map(|_| draw(sequence, p)));
    values
}

/// The elements of `values`, built by the adapter.
pub fn elements(adapter: &PrimeAdapter, values: &[u64]) -> Vec<PrimeResidue> {
    values.iter().map(|value| adapter.element(value)).collect()
}

/// The ring $\mathbb F_p\[x\]$ of the checks.
pub fn polynomial_ring(adapter: &PrimeAdapter) -> PolynomialRing<PrimeField> {
    ok(
        "F_p[x]",
        PolynomialRing::new(*adapter.field(), VARIABLE, &mut roomy()),
    )
}

/// The zero polynomial and `count` generated polynomials of degree at most
/// eight, whose coefficients are drawn residues.
pub fn polynomial_inputs(
    ring: &PolynomialRing<PrimeField>,
    adapter: &PrimeAdapter,
    sequence: &mut Sequence,
    count: usize,
) -> Vec<Polynomial<PrimeField>> {
    let view = Polynomials { ring, adapter };
    let p = adapter.modulus();
    polynomials(&view, sequence, count, 8, &mut |sequence| {
        adapter.element(&draw(sequence, p))
    })
}

/// The polynomial with the coefficients `coefficients` from degree 0 up,
/// each reduced modulo $p$.
fn dense(
    view: &Polynomials<'_, PrimeField, PrimeAdapter>,
    coefficients: &[i64],
) -> Polynomial<PrimeField> {
    let model = view.adapter.model();
    let terms: Vec<(u64, PrimeResidue)> = coefficients
        .iter()
        .zip(0_u64..)
        .map(|(&c, degree)| (degree, view.adapter.element(&model.integer(i128::from(c)))))
        .collect();
    view.polynomial(&terms, &mut roomy())
}

/// Every polynomial of degree at most `max_degree`, the zero polynomial
/// included: $p^{d + 1}$ of them for the degree $d$.
pub fn every_polynomial(
    ring: &PolynomialRing<PrimeField>,
    adapter: &PrimeAdapter,
    max_degree: u32,
) -> Vec<Polynomial<PrimeField>> {
    let view = Polynomials { ring, adapter };
    let p = adapter.modulus();
    (0..p.pow(max_degree + 1))
        .map(|code| {
            let coefficients: Vec<i64> = (0..=max_degree)
                .map(|place| i64::try_from(code / p.pow(place) % p).unwrap())
                .collect();
            dense(&view, &coefficients)
        })
        .collect()
}

/// The element pairs of the accounting checks: $(3, p - 2)$,
/// $(p - 1, p - 1)$, $(5, 0)$, $(1, 2)$ and $(p - 2, 3)$, each integer
/// reduced modulo $p$; the zero divisor of $(5, 0)$ is zero in every field.
pub fn accounting_elements(adapter: &PrimeAdapter) -> Vec<(PrimeResidue, PrimeResidue)> {
    let p = i64::try_from(adapter.modulus()).unwrap();
    let element = |n: i64| adapter.element(&adapter.model().integer(i128::from(n)));
    [(3, p - 2), (p - 1, p - 1), (5, 0), (1, 2), (p - 2, 3)]
        .iter()
        .map(|&(a, b)| (element(a), element(b)))
        .collect()
}

/// The polynomial pairs of the accounting checks of the earlier
/// implementation, from degree 0 up and reduced modulo $p$:
/// $1 + 2 x + 3 x^2 + x^3$ and $(p - 3) + x$, $4 x^2 + x^4$ and $2 + x^2$,
/// $6 + x$ and 0, and 0 and $1 + x$.
pub fn accounting_polynomials(
    ring: &PolynomialRing<PrimeField>,
    adapter: &PrimeAdapter,
) -> Vec<(Polynomial<PrimeField>, Polynomial<PrimeField>)> {
    let view = Polynomials { ring, adapter };
    let p = i64::try_from(adapter.modulus()).unwrap();
    let polynomial = |coefficients: &[i64]| dense(&view, coefficients);
    vec![
        (polynomial(&[1, 2, 3, 1]), polynomial(&[p - 3, 1])),
        (polynomial(&[0, 0, 4, 0, 1]), polynomial(&[2, 0, 1])),
        (polynomial(&[6, 1]), polynomial(&[])),
        (polynomial(&[]), polynomial(&[1, 1])),
    ]
}
