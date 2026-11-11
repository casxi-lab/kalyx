//! The property-testing tool of the coefficient fields, through the public
//! interface of the library.
//!
//! The checks are generic over two layers of this module: [`RingLayer`],
//! the operations of a ring with one and its zero test, and [`FieldLayer`],
//! the inverse and the quotient of a field. The parents of
//! the library enter both through one wrapper, [`Library`], whose every
//! operation is the method of `CoefficientRing` or `CoefficientField` and
//! which adds none; the coefficient traits are sealed, so the only other
//! implementation of the ring layer is a parent of the tests that is
//! deliberately not commutative, on which the ring axioms must fail. The
//! checks of a ring run on the ring layer alone, and those of a field add
//! the field layer.
//!
//! A parent is checked with an adapter, [`Inspect`], which gives no
//! operation: it names the parent and its characteristic, and reads the
//! stored form of an element, whether it is canonical and whether it is the
//! form of zero. An adapter with an independent [`Model`] of the parent,
//! [`Modelled`], also reads the value of a small element in the model and
//! its display text, and builds inputs, the element of a model value and
//! large elements, without the operations under test.
//! Every check judges results by independent evidence: ring identities,
//! values known by construction, or the model, whose arithmetic does not use
//! the code under test.
//!
//! The checks of elements and maps are in `elements`, those of polynomials
//! in `univariate` and those of work accounting and cancellation in
//! `accounting`; the adapter of $\mathbb{Q}$ with its model and its inputs is
//! in `rationals`. This module holds the layers, the adapter and model
//! traits, the integer model, and the helpers and generators of the checks.

pub mod accounting;
pub mod elements;
pub mod rationals;
pub mod univariate;

use std::convert::Infallible;
use std::fmt;

use kalyx::coefficient::{CoefficientField, CoefficientRing, ZeroTest};
use kalyx::context::CancelFlag;
use kalyx::number::{Integer, Rational};
use kalyx::polynomial::{Polynomial, PolynomialRing};
use kalyx::{Context, Error, Limits, Result};

use crate::support::Sequence;

/// The work budget of each case of a property check, far above the work of
/// the largest case. A regression that stops terminating then fails with
/// `ResourceLimit` instead of running on. The accounting checks set their
/// own budgets.
pub const PROPERTY_WORK: u64 = 10_000_000;

// ---------------------------------------------------------------------------
// The layers

/// The ring layer of the checks: the operations of a ring with one, whose
/// commutativity the ring axioms check, and its zero test, each taking the
/// request context last.
pub trait RingLayer {
    /// The elements; they need no equality, since the checks compare their
    /// stored forms through the adapter.
    type Element: Clone;
    /// Why the zero test could not decide.
    type Undecided;

    fn zero(&self, context: &mut Context) -> Result<Self::Element>;
    fn one(&self, context: &mut Context) -> Result<Self::Element>;
    /// The image $n \cdot 1$ of the integer `n`.
    #[allow(
        clippy::wrong_self_convention,
        reason = "the name of the library trait, whose image of an integer needs the ring"
    )]
    fn from_integer(&self, n: &Integer, context: &mut Context) -> Result<Self::Element>;
    fn negate(&self, a: &Self::Element, context: &mut Context) -> Result<Self::Element>;
    fn add(
        &self,
        a: &Self::Element,
        b: &Self::Element,
        context: &mut Context,
    ) -> Result<Self::Element>;
    fn subtract(
        &self,
        a: &Self::Element,
        b: &Self::Element,
        context: &mut Context,
    ) -> Result<Self::Element>;
    fn multiply(
        &self,
        a: &Self::Element,
        b: &Self::Element,
        context: &mut Context,
    ) -> Result<Self::Element>;
    fn zero_test(
        &self,
        a: &Self::Element,
        context: &mut Context,
    ) -> Result<ZeroTest<Self::Undecided>>;
}

/// The field layer of the checks: the inverse and the quotient, which fail
/// on a zero element or divisor.
pub trait FieldLayer: RingLayer {
    fn inverse(&self, a: &Self::Element, context: &mut Context) -> Result<Self::Element>;
    fn divide(
        &self,
        a: &Self::Element,
        b: &Self::Element,
        context: &mut Context,
    ) -> Result<Self::Element>;
}

/// A parent `K` of the library as the ring layer, and as the field layer
/// when it is a field. Every operation is the method of the library trait
/// with the same name; the wrapper adds none.
#[derive(Clone, Copy, Debug)]
pub struct Library<K>(pub K);

impl<K: CoefficientRing> RingLayer for Library<K> {
    type Element = K::Element;
    type Undecided = K::Undecided;

    fn zero(&self, context: &mut Context) -> Result<K::Element> {
        self.0.zero(context)
    }

    fn one(&self, context: &mut Context) -> Result<K::Element> {
        self.0.one(context)
    }

    fn from_integer(&self, n: &Integer, context: &mut Context) -> Result<K::Element> {
        self.0.from_integer(n, context)
    }

    fn negate(&self, a: &K::Element, context: &mut Context) -> Result<K::Element> {
        self.0.negate(a, context)
    }

    fn add(&self, a: &K::Element, b: &K::Element, context: &mut Context) -> Result<K::Element> {
        self.0.add(a, b, context)
    }

    fn subtract(
        &self,
        a: &K::Element,
        b: &K::Element,
        context: &mut Context,
    ) -> Result<K::Element> {
        self.0.subtract(a, b, context)
    }

    fn multiply(
        &self,
        a: &K::Element,
        b: &K::Element,
        context: &mut Context,
    ) -> Result<K::Element> {
        self.0.multiply(a, b, context)
    }

    fn zero_test(&self, a: &K::Element, context: &mut Context) -> Result<ZeroTest<K::Undecided>> {
        self.0.zero_test(a, context)
    }
}

impl<K: CoefficientField> FieldLayer for Library<K> {
    fn inverse(&self, a: &K::Element, context: &mut Context) -> Result<K::Element> {
        self.0.inverse(a, context)
    }

    fn divide(&self, a: &K::Element, b: &K::Element, context: &mut Context) -> Result<K::Element> {
        self.0.divide(a, b, context)
    }
}

// ---------------------------------------------------------------------------
// Adapters and models

/// The elements of the ring layer of the adapter `A`.
pub type Element<A> = <<A as Inspect>::Ring as RingLayer>::Element;

/// The values of the model of the adapter `A`.
pub type Value<A> = <<A as Modelled>::Model as Model>::Value;

/// The adapter of a parent under the checks: no operation, only its name,
/// its characteristic and readings of the stored forms of its elements,
/// which the canonical-form checks take instead of the operations under
/// test.
pub trait Inspect {
    /// The ring layer of the parent.
    type Ring: RingLayer;

    fn ring(&self) -> &Self::Ring;
    fn label(&self) -> String;
    /// Zero for characteristic zero, otherwise the prime $p$.
    fn characteristic(&self) -> u64;
    /// The text of the stored form, which a canonical form makes unique.
    fn representation(&self, a: &<Self::Ring as RingLayer>::Element) -> String;
    /// Whether the stored form is canonical.
    fn canonical(&self, a: &<Self::Ring as RingLayer>::Element) -> bool;
    /// Whether the stored form is that of zero.
    fn stored_zero(&self, a: &<Self::Ring as RingLayer>::Element) -> bool;
}

/// An independent model of a commutative ring with one: its arithmetic in
/// the test code. Its operations panic where the model cannot represent the
/// result, so the checks give it only operands it serves.
pub trait Model {
    type Value: Clone + PartialEq + fmt::Debug + fmt::Display;

    fn label(&self) -> String;
    fn zero(&self) -> Self::Value;
    fn one(&self) -> Self::Value;
    fn integer(&self, n: i128) -> Self::Value;
    fn add(&self, a: &Self::Value, b: &Self::Value) -> Self::Value;
    fn subtract(&self, a: &Self::Value, b: &Self::Value) -> Self::Value;
    fn multiply(&self, a: &Self::Value, b: &Self::Value) -> Self::Value;
    fn negate(&self, a: &Self::Value) -> Self::Value;
}

/// An independent model of a field.
pub trait FieldModel: Model {
    /// The inverse, or `None` for zero.
    fn inverse(&self, a: &Self::Value) -> Option<Self::Value>;

    /// Integers $n$ and $d \ne 0$ with $n \cdot 1 / d \cdot 1$ equal to
    /// `value`, both scaled by `scale`; $d \cdot 1$ must be nonzero in the
    /// field.
    fn fraction(&self, value: &Self::Value, scale: i64) -> (Integer, Integer);
}

/// An adapter with an independent model of its parent.
pub trait Modelled: Inspect {
    type Model: Model;

    fn model(&self) -> &Self::Model;
    /// The value in the model of a small element, read from its stored form.
    fn value(&self, a: &Element<Self>) -> Value<Self>;
    /// The element of `value`, built by the adapter without the operations
    /// under test.
    fn element(&self, value: &Value<Self>) -> Element<Self>;
    /// Whether `a` is `value`, judged by the model.
    fn agrees(&self, a: &Element<Self>, value: &Value<Self>) -> bool;
    /// The display text of `a`.
    fn text(&self, a: &Element<Self>) -> String;
    /// A small value, sometimes zero, one or an integer.
    fn sample(&self, random: &mut Sequence) -> Value<Self>;
    /// A large element, built by the adapter without the operations under
    /// test.
    fn large(&self, random: &mut Sequence) -> Element<Self>;
}

/// The integers as `i128`, the source of the map into a parent. Their
/// arithmetic panics on overflow.
pub struct Integers;

impl Model for Integers {
    type Value = i128;

    fn label(&self) -> String {
        "the i128 integers".into()
    }

    fn zero(&self) -> i128 {
        0
    }

    fn one(&self) -> i128 {
        1
    }

    fn integer(&self, n: i128) -> i128 {
        n
    }

    fn add(&self, a: &i128, b: &i128) -> i128 {
        a.checked_add(*b).unwrap()
    }

    fn subtract(&self, a: &i128, b: &i128) -> i128 {
        a.checked_sub(*b).unwrap()
    }

    fn multiply(&self, a: &i128, b: &i128) -> i128 {
        a.checked_mul(*b).unwrap()
    }

    fn negate(&self, a: &i128) -> i128 {
        a.checked_neg().unwrap()
    }
}

/// The `Integer` of `n`. An `Integer` is built only from an `i64` or a
/// `u64`, so a wider value is read as the decimal literal of its absolute
/// value, negated when `n` is negative; the integer is the numerator.
pub fn integer_of(n: i128) -> Integer {
    let context = &mut roomy();
    let magnitude = ok(
        "the literal of |n|",
        Rational::parse_decimal(&n.unsigned_abs().to_string(), context),
    );
    let value = if n < 0 {
        ok("-|n|", magnitude.negate(context))
    } else {
        magnitude
    };
    value.numerator().clone()
}

// ---------------------------------------------------------------------------
// Helpers of the checks

/// A label that is formatted only when a case fails.
pub struct Lazy<F: Fn(&mut fmt::Formatter<'_>) -> fmt::Result>(pub F);

impl<F: Fn(&mut fmt::Formatter<'_>) -> fmt::Result> fmt::Display for Lazy<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (self.0)(f)
    }
}

/// A context for one case of a property check: default limits, except the
/// work budget `PROPERTY_WORK` and room for the coefficient growth of
/// products and powers. Each case takes a fresh context, so its budget does
/// not depend on the number of cases.
pub fn roomy() -> Context {
    Context::new(
        Limits::new()
            .with_max_work(PROPERTY_WORK)
            .with_max_integer_bits(1 << 16)
            .with_max_nodes(1 << 20)
            .with_max_storage_bytes(1 << 26),
        CancelFlag::new(),
    )
}

/// The value of a successful operation.
pub fn ok<T>(what: &str, result: Result<T>) -> T {
    match result {
        Ok(value) => value,
        Err(error) => panic!("{what}: unexpected error {error:?}"),
    }
}

/// The error of a failed operation.
pub fn failure<T>(what: &str, result: Result<T>) -> Error {
    match result {
        Ok(_) => panic!("{what}: expected an error"),
        Err(error) => error,
    }
}

/// The element of a successful operation, which must be canonical.
pub fn checked<A: Inspect>(adapter: &A, what: &str, result: Result<Element<A>>) -> Element<A> {
    let value = ok(what, result);
    assert!(
        adapter.canonical(&value),
        "{}: {what} gave the noncanonical {}",
        adapter.label(),
        adapter.representation(&value)
    );
    value
}

/// The zero test of an exact ring: zero or nonzero, never undecided, and in
/// agreement with the stored form.
pub fn exact_zero_test<A: Inspect>(adapter: &A, a: &Element<A>, context: &mut Context) -> bool {
    let zero = match ok("zero test", adapter.ring().zero_test(a, context)) {
        ZeroTest::Zero => true,
        ZeroTest::Nonzero => false,
        ZeroTest::Undecided(_) => panic!(
            "{}: the zero test of an exact ring did not decide for {}",
            adapter.label(),
            adapter.representation(a)
        ),
    };
    assert_eq!(
        zero,
        adapter.stored_zero(a),
        "{}: the zero test disagrees with the stored form of {}",
        adapter.label(),
        adapter.representation(a)
    );
    zero
}

/// The elements of the ring layer of an adapter, whose operations must
/// succeed and give canonical elements, compared by their stored forms.
pub struct Elements<'a, A>(pub &'a A);

impl<A: Inspect> Elements<'_, A> {
    pub fn zero(&self, context: &mut Context) -> Element<A> {
        checked(self.0, "0", self.0.ring().zero(context))
    }

    pub fn one(&self, context: &mut Context) -> Element<A> {
        checked(self.0, "1", self.0.ring().one(context))
    }

    pub fn integer(&self, n: &Integer, context: &mut Context) -> Element<A> {
        checked(self.0, "n * 1", self.0.ring().from_integer(n, context))
    }

    pub fn add(&self, a: &Element<A>, b: &Element<A>, context: &mut Context) -> Element<A> {
        checked(self.0, "a + b", self.0.ring().add(a, b, context))
    }

    pub fn subtract(&self, a: &Element<A>, b: &Element<A>, context: &mut Context) -> Element<A> {
        checked(self.0, "a - b", self.0.ring().subtract(a, b, context))
    }

    pub fn negate(&self, a: &Element<A>, context: &mut Context) -> Element<A> {
        checked(self.0, "-a", self.0.ring().negate(a, context))
    }

    pub fn multiply(&self, a: &Element<A>, b: &Element<A>, context: &mut Context) -> Element<A> {
        checked(self.0, "a b", self.0.ring().multiply(a, b, context))
    }

    /// Whether the stored forms of `a` and `b` are the same.
    pub fn same(&self, a: &Element<A>, b: &Element<A>) -> bool {
        self.0.representation(a) == self.0.representation(b)
    }

    /// Whether `a` and `b` are equal in the ring: their difference is zero.
    pub fn equal(&self, a: &Element<A>, b: &Element<A>, context: &mut Context) -> bool {
        let difference = self.subtract(a, b, context);
        exact_zero_test(self.0, &difference, context)
    }
}

impl<A: Inspect> Elements<'_, A>
where
    A::Ring: FieldLayer,
{
    pub fn inverse(&self, a: &Element<A>, context: &mut Context) -> Element<A> {
        checked(self.0, "1 / a", self.0.ring().inverse(a, context))
    }

    pub fn divide(&self, a: &Element<A>, b: &Element<A>, context: &mut Context) -> Element<A> {
        checked(self.0, "a / b", self.0.ring().divide(a, b, context))
    }
}

/// The polynomials of a ring over the parent of an adapter, through the
/// public methods of `PolynomialRing`. Every result must be canonical, and
/// polynomials are compared by their degrees and by the coefficient ring:
/// two coefficients are equal when their difference is zero.
pub struct Polynomials<'a, K: CoefficientRing, A> {
    pub ring: &'a PolynomialRing<K>,
    pub adapter: &'a A,
}

impl<K, A> Polynomials<'_, K, A>
where
    K: CoefficientRing<Undecided = Infallible>,
    A: Inspect<Ring = Library<K>>,
{
    /// The polynomial of a successful operation, which must be canonical.
    pub fn checked(
        &self,
        what: &str,
        result: Result<Polynomial<K>>,
        context: &mut Context,
    ) -> Polynomial<K> {
        let value = ok(what, result);
        assert!(
            self.canonical(&value, context),
            "{}: {what} gave the noncanonical {}",
            self.adapter.label(),
            self.representation(&value)
        );
        value
    }

    /// Whether `p` is canonical: its degrees strictly increase, its
    /// coefficients are canonical and the zero test finds none zero, its
    /// degree is its last degree, and it is zero exactly when it has no
    /// term.
    pub fn canonical(&self, p: &Polynomial<K>, context: &mut Context) -> bool {
        let (degrees, coefficients) = (p.degrees(), p.coefficients());
        let increasing = degrees.windows(2).all(|pair| pair[0] < pair[1]);
        let nonzero = coefficients.iter().all(|c| {
            self.adapter.canonical(c)
                && ok(
                    "zero test",
                    self.ring.coefficient_ring().zero_test(c, context),
                ) == ZeroTest::Nonzero
        });
        increasing
            && nonzero
            && degrees.len() == coefficients.len()
            && p.degree() == degrees.last().copied()
            && p.is_zero() == degrees.is_empty()
    }

    /// The text of the stored form: each degree with the stored form of its
    /// coefficient.
    pub fn representation(&self, p: &Polynomial<K>) -> String {
        let terms: Vec<String> = p
            .degrees()
            .iter()
            .zip(p.coefficients())
            .map(|(degree, c)| format!("{degree}: {}", self.adapter.representation(c)))
            .collect();
        format!("[{}]", terms.join(", "))
    }

    /// Whether `a` and `b` are equal: the same degrees, and coefficients
    /// whose difference the coefficient ring finds zero.
    pub fn equal(&self, a: &Polynomial<K>, b: &Polynomial<K>, context: &mut Context) -> bool {
        let field = self.ring.coefficient_ring();
        a.degrees() == b.degrees()
            && a.coefficients().iter().zip(b.coefficients()).all(|(x, y)| {
                let difference = ok("a - b", field.subtract(x, y, context));
                ok("zero test", field.zero_test(&difference, context)) == ZeroTest::Zero
            })
    }

    pub fn zero(&self, context: &mut Context) -> Polynomial<K> {
        let result = self.ring.zero(context);
        self.checked("0", result, context)
    }

    pub fn one(&self, context: &mut Context) -> Polynomial<K> {
        let result = self.ring.one(context);
        self.checked("1", result, context)
    }

    pub fn constant(&self, value: &K::Element, context: &mut Context) -> Polynomial<K> {
        let result = self.ring.constant(value, context);
        self.checked("constant", result, context)
    }

    pub fn add(
        &self,
        a: &Polynomial<K>,
        b: &Polynomial<K>,
        context: &mut Context,
    ) -> Polynomial<K> {
        let result = self.ring.add(a, b, context);
        self.checked("a + b", result, context)
    }

    pub fn subtract(
        &self,
        a: &Polynomial<K>,
        b: &Polynomial<K>,
        context: &mut Context,
    ) -> Polynomial<K> {
        let result = self.ring.subtract(a, b, context);
        self.checked("a - b", result, context)
    }

    pub fn multiply(
        &self,
        a: &Polynomial<K>,
        b: &Polynomial<K>,
        context: &mut Context,
    ) -> Polynomial<K> {
        let result = self.ring.multiply(a, b, context);
        self.checked("a b", result, context)
    }

    pub fn power(&self, a: &Polynomial<K>, exponent: u64, context: &mut Context) -> Polynomial<K> {
        let result = self.ring.power(a, exponent, context);
        self.checked("a^k", result, context)
    }

    pub fn derivative(&self, a: &Polynomial<K>, context: &mut Context) -> Polynomial<K> {
        let result = self.ring.derivative(a, context);
        self.checked("a'", result, context)
    }

    /// The polynomial with the terms `terms`, of distinct degrees, assembled
    /// from constants, the generator, its powers, products and sums. A zero
    /// coefficient gives no term.
    pub fn polynomial(&self, terms: &[(u64, K::Element)], context: &mut Context) -> Polynomial<K> {
        let x = {
            let result = self.ring.generator(context);
            self.checked("x", result, context)
        };
        let mut result = self.zero(context);
        for (degree, value) in terms {
            let monomial = self.power(&x, *degree, context);
            let coefficient = self.constant(value, context);
            let term = self.multiply(&coefficient, &monomial, context);
            result = self.add(&result, &term, context);
        }
        result
    }
}

/// Every index pair when there are at most `count`, otherwise `count` drawn
/// pairs.
pub fn pairs(len: usize, count: usize, sequence: &mut Sequence) -> Vec<(usize, usize)> {
    if len * len <= count {
        return (0..len)
            .flat_map(|i| (0..len).map(move |j| (i, j)))
            .collect();
    }
    (0..count)
        .map(|_| (sequence.index(len), sequence.index(len)))
        .collect()
}

/// Every index triple when there are at most `count`, otherwise `count`
/// drawn triples.
pub fn triples(len: usize, count: usize, sequence: &mut Sequence) -> Vec<(usize, usize, usize)> {
    if len * len * len <= count {
        return (0..len)
            .flat_map(|i| (0..len).flat_map(move |j| (0..len).map(move |k| (i, j, k))))
            .collect();
    }
    (0..count)
        .map(|_| {
            (
                sequence.index(len),
                sequence.index(len),
                sequence.index(len),
            )
        })
        .collect()
}

/// The zero polynomial, then `count` generated polynomials of degree at most
/// `max_degree`: in turn monomials and constants, dense supports, sparse
/// supports of up to three terms and random supports. `coefficient` may
/// return zero, which leaves no term.
pub fn polynomials<K, A>(
    view: &Polynomials<'_, K, A>,
    sequence: &mut Sequence,
    count: usize,
    max_degree: u64,
    coefficient: &mut dyn FnMut(&mut Sequence) -> K::Element,
) -> Vec<Polynomial<K>>
where
    K: CoefficientRing<Undecided = Infallible>,
    A: Inspect<Ring = Library<K>>,
{
    /// A degree in `0..=high`.
    fn draw(sequence: &mut Sequence, high: u64) -> u64 {
        u64::try_from(sequence.next_in(0, i64::try_from(high).unwrap())).unwrap()
    }

    let context = &mut roomy();
    let mut result = vec![view.zero(context)];
    for index in 0..count {
        let degree = draw(sequence, max_degree);
        let mut support: Vec<u64> = match index % 4 {
            0 => vec![degree],
            1 => (0..=degree).collect(),
            2 => {
                let mut support = vec![draw(sequence, degree), draw(sequence, degree)];
                support.push(degree);
                support
            }
            _ => {
                let mut support: Vec<u64> =
                    (0..degree).filter(|_| draw(sequence, 1) == 1).collect();
                support.push(degree);
                support
            }
        };
        support.sort_unstable();
        support.dedup();
        let terms: Vec<(u64, K::Element)> = support
            .into_iter()
            .map(|degree| (degree, coefficient(sequence)))
            .collect();
        result.push(view.polynomial(&terms, context));
    }
    result
}
