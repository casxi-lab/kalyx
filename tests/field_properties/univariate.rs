//! The polynomial checks of the tool, over the operations that the
//! polynomials have: the univariate laws, and agreement with an independent
//! model applied coefficient by coefficient.
//!
//! The checks are generic over every coefficient ring of the library whose
//! zero test decides, and reach the polynomials only through the public
//! methods of `PolynomialRing` and the accessors `degree`, `degrees` and
//! `coefficients`. They compare two polynomials by their degrees and their
//! coefficients through `subtract` and `zero_test` of the coefficient ring,
//! never by `==`.

use std::convert::Infallible;

use kalyx::coefficient::CoefficientRing;
use kalyx::polynomial::{Polynomial, PolynomialRing};

use super::elements::unique_forms;
use super::{Inspect, Lazy, Library, Model, Modelled, Polynomials, Value, roomy};
use crate::support::case;

/// The interpretation of a polynomial in the model: its coefficients from
/// degree zero up to its degree, read through `degrees` and
/// `coefficients`.
fn interpret<K, A>(adapter: &A, p: &Polynomial<K>) -> Vec<Value<A>>
where
    K: CoefficientRing,
    A: Modelled<Ring = Library<K>>,
{
    let model = adapter.model();
    let length = p
        .degree()
        .map_or(0, |degree| usize::try_from(degree).unwrap() + 1);
    let mut values = vec![model.zero(); length];
    for (degree, c) in p.degrees().iter().zip(p.coefficients()) {
        values[usize::try_from(*degree).unwrap()] = adapter.value(c);
    }
    values
}

/// Whether two coefficient lists in the model denote the same polynomial;
/// missing coefficients are zero.
fn same_polynomial<M: Model>(model: &M, a: &[M::Value], b: &[M::Value]) -> bool {
    let zero = model.zero();
    (0..a.len().max(b.len())).all(|i| a.get(i).unwrap_or(&zero) == b.get(i).unwrap_or(&zero))
}

fn model_sum<M: Model>(model: &M, a: &[M::Value], b: &[M::Value]) -> Vec<M::Value> {
    let zero = model.zero();
    (0..a.len().max(b.len()))
        .map(|i| model.add(a.get(i).unwrap_or(&zero), b.get(i).unwrap_or(&zero)))
        .collect()
}

fn model_difference<M: Model>(model: &M, a: &[M::Value], b: &[M::Value]) -> Vec<M::Value> {
    let zero = model.zero();
    (0..a.len().max(b.len()))
        .map(|i| model.subtract(a.get(i).unwrap_or(&zero), b.get(i).unwrap_or(&zero)))
        .collect()
}

/// The degree of a coefficient list in the model: the index of its last
/// nonzero value.
fn model_degree<M: Model>(model: &M, a: &[M::Value]) -> Option<u64> {
    let zero = model.zero();
    a.iter()
        .rposition(|c| *c != zero)
        .map(|i| u64::try_from(i).unwrap())
}

fn model_product<M: Model>(model: &M, a: &[M::Value], b: &[M::Value]) -> Vec<M::Value> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut result = vec![model.zero(); a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        for (j, y) in b.iter().enumerate() {
            let term = model.multiply(x, y);
            result[i + j] = model.add(&result[i + j], &term);
        }
    }
    result
}

/// The derivative in the model: the coefficient $i c_i$ at degree $i - 1$.
fn model_derivative<M: Model>(model: &M, a: &[M::Value]) -> Vec<M::Value> {
    a.iter()
        .enumerate()
        .skip(1)
        .map(|(i, c)| model.multiply(&model.integer(i128::try_from(i).unwrap()), c))
        .collect()
}

/// Asserts that `p` has the coefficients `expected` in the model, and the
/// degree of their last nonzero value.
fn assert_model<K, A>(adapter: &A, p: &Polynomial<K>, expected: &[Value<A>], what: &str)
where
    K: CoefficientRing,
    A: Modelled<Ring = Library<K>>,
{
    let model = adapter.model();
    let actual = interpret(adapter, p);
    assert!(same_polynomial(model, &actual, expected), "{what}");
    assert_eq!(
        p.degree(),
        model_degree(model, expected),
        "the degree of {what}"
    );
}

/// The univariate laws on `polynomials`, over the operations that the
/// polynomials have. For each polynomial: it is canonical, only the zero
/// polynomial has no degree, $p - p = 0$, the derivative of a constant is
/// zero and that of a polynomial of positive degree has a lower degree, and
/// $p^0$ to $p^4$ are the repeated products. For each pair: $a + b = b + a$,
/// $(a + b) - b = a$, $a b = b a$ and $(a b)' = a' b + a b'$. For each
/// triple: $(a b) c = a (b c)$ and $a (b + c) = a b + a c$. Every result is
/// canonical.
pub fn polynomial_laws<K, A>(
    ring: &PolynomialRing<K>,
    adapter: &A,
    polynomials: &[Polynomial<K>],
    pairs: &[(usize, usize)],
    triples: &[(usize, usize, usize)],
) where
    K: CoefficientRing<Undecided = Infallible>,
    A: Inspect<Ring = Library<K>>,
{
    let view = Polynomials { ring, adapter };
    let label = adapter.label();
    let context = &mut roomy();
    let zero = view.zero(context);
    let unit = view.one(context);
    assert_eq!(zero.degree(), None, "the zero polynomial has no degree");
    for (index, p) in polynomials.iter().enumerate() {
        case(
            Lazy(|f| {
                let p = view.representation(p);
                write!(f, "polynomials over {label}: polynomial {index}, {p}")
            }),
            || {
                let context = &mut roomy();
                assert!(view.canonical(p, context), "noncanonical input");
                let degree = p.degree();
                assert_eq!(
                    degree.is_none(),
                    view.equal(p, &zero, context),
                    "only zero has no degree"
                );
                let difference = view.subtract(p, p, context);
                assert!(view.equal(&difference, &zero, context), "p - p = 0");
                let derivative = view.derivative(p, context);
                match degree {
                    Some(d) if d > 0 => {
                        assert!(derivative.degree() < Some(d), "deg p' < deg p");
                    }
                    _ => assert!(view.equal(&derivative, &zero, context), "c' = 0"),
                }
                let mut repeated = unit.clone();
                for exponent in 0..=4 {
                    let power = view.power(p, exponent, context);
                    assert!(view.equal(&power, &repeated, context), "p^{exponent}");
                    repeated = view.multiply(&repeated, p, context);
                }
            },
        );
    }
    for &(i, j) in pairs {
        let (a, b) = (&polynomials[i], &polynomials[j]);
        case(
            Lazy(|f| write!(f, "polynomials over {label}: polynomials {i}, {j}")),
            || {
                let context = &mut roomy();
                let sum = view.add(a, b, context);
                let reversed = view.add(b, a, context);
                assert!(view.equal(&sum, &reversed, context), "a + b = b + a");
                let back = view.subtract(&sum, b, context);
                assert!(view.equal(&back, a, context), "(a + b) - b = a");
                let product = view.multiply(a, b, context);
                let reversed = view.multiply(b, a, context);
                assert!(view.equal(&product, &reversed, context), "a b = b a");
                let left = view.multiply(&view.derivative(a, context), b, context);
                let right = view.multiply(a, &view.derivative(b, context), context);
                let expected = view.add(&left, &right, context);
                let derivative = view.derivative(&product, context);
                assert!(
                    view.equal(&derivative, &expected, context),
                    "(a b)' = a' b + a b'"
                );
            },
        );
    }
    for &(i, j, k) in triples {
        let (a, b, c) = (&polynomials[i], &polynomials[j], &polynomials[k]);
        case(
            Lazy(|f| write!(f, "polynomials over {label}: polynomials {i}, {j}, {k}")),
            || {
                let context = &mut roomy();
                let ab = view.multiply(a, b, context);
                let bc = view.multiply(b, c, context);
                let left = view.multiply(&ab, c, context);
                let right = view.multiply(a, &bc, context);
                assert!(view.equal(&left, &right, context), "(a b) c = a (b c)");
                let sum = view.add(b, c, context);
                let ac = view.multiply(a, c, context);
                let left = view.multiply(a, &sum, context);
                let right = view.add(&ab, &ac, context);
                assert!(view.equal(&left, &right, context), "a (b + c) = a b + a c");
            },
        );
    }
}

/// The polynomial operations against the model of the adapter applied
/// coefficient by coefficient: the derivative of each polynomial, and the
/// sum, the difference and the product of each pair, are formed in the
/// model; and among these results two stored forms are equal exactly when
/// their coefficient values are.
pub fn polynomial_model_agreement<K, A>(
    ring: &PolynomialRing<K>,
    adapter: &A,
    polynomials: &[Polynomial<K>],
    pairs: &[(usize, usize)],
) where
    K: CoefficientRing<Undecided = Infallible>,
    A: Modelled<Ring = Library<K>>,
{
    let view = Polynomials { ring, adapter };
    let model = adapter.model();
    let label = adapter.label();
    let mut results: Vec<Polynomial<K>> = Vec::new();
    for (index, p) in polynomials.iter().enumerate() {
        case(
            Lazy(|f| write!(f, "polynomials over {label}: polynomial {index}")),
            || {
                let context = &mut roomy();
                let x = interpret(adapter, p);
                let derivative = view.derivative(p, context);
                assert_model(adapter, &derivative, &model_derivative(model, &x), "p'");
                results.push(derivative);
            },
        );
    }
    for &(i, j) in pairs {
        let (a, b) = (&polynomials[i], &polynomials[j]);
        case(
            Lazy(|f| {
                let model = model.label();
                write!(
                    f,
                    "polynomials over {label} against {model}: polynomials {i}, {j}"
                )
            }),
            || {
                let context = &mut roomy();
                let (x, y) = (interpret(adapter, a), interpret(adapter, b));
                let sum = view.add(a, b, context);
                assert_model(adapter, &sum, &model_sum(model, &x, &y), "a + b");
                let difference = view.subtract(a, b, context);
                let expected = model_difference(model, &x, &y);
                assert_model(adapter, &difference, &expected, "a - b");
                let product = view.multiply(a, b, context);
                assert_model(adapter, &product, &model_product(model, &x, &y), "a b");
                results.extend([sum, difference, product]);
            },
        );
    }
    let representations: Vec<String> = results.iter().map(|p| view.representation(p)).collect();
    let values: Vec<String> = results
        .iter()
        .map(|p| {
            let terms: Vec<String> = interpret(adapter, p)
                .iter()
                .map(ToString::to_string)
                .collect();
            terms.join(", ")
        })
        .collect();
    unique_forms(
        &format!("polynomials over {label}"),
        &representations,
        &values,
    );
}
