//! The terms of a polynomial and the checks of a polynomial against the
//! limits of the context.
//!
//! A polynomial is stored as two lists of the same length: the degrees, in
//! increasing order without repetitions, and the coefficients, none of which
//! is zero. The list keeps the measure of its storage cost as it grows, so
//! the cost of a polynomial is known in constant time, before the polynomial
//! is admitted and whenever it is asked for. The measure leaves out the
//! bytes of the variable name, which belongs to the ring, and counts how
//! often the name is written instead.
//!
//! The storage formula of a univariate polynomial with the variable name of
//! $\ell$ bytes is that of the architecture, for a coefficient $c$ whose
//! cost $(n_c, b_c)$ is the `measure` of its coefficient ring, which is
//! $(1, \mathrm{rb}(c))$ for a rational:
//!
//! - the zero polynomial costs $(1, 4)$, the cost of the number 0;
//! - a term of degree 0 costs $(n_c, b_c)$, a term of degree 1
//!   $(n_c + 2, b_c + \ell + 4)$, and a term of degree $k \ge 2$
//!   $(n_c + 4, b_c + \ell + \lvert k \rvert + 12)$, where $\lvert k \rvert$
//!   is the bit length of $k$;
//! - each addition between two terms costs $(1, 4)$;
//! - a polynomial other than zero without a term of positive degree, a
//!   constant, writes the variable name once, $(0, \ell)$.

use crate::coefficient::CoefficientRing;
use crate::context::Storage;
use crate::{Context, Error, FaultKind, LimitField, LimitScope, Result};

/// The largest degree of a polynomial: the largest `i64`, the width of the
/// exponents of the term core, so that every degree is the exponent of a
/// term. It is the machine width that bounds `max_exponent` for degrees.
pub(super) const DEGREE_WIDTH: u64 = i64::MAX as u64;

/// The cost of the zero polynomial: the cost of the number 0, one node and
/// $\lvert 0 \rvert + \lvert 1 \rvert + 3 = 4$ bytes.
const ZERO_COST: Storage = Storage::new(1, 4);

/// The nodes and bytes that a term of degree 1 adds to its coefficient,
/// besides the variable name: the symbol and the product, and the operator
/// of the product.
const LINEAR_EXTRA: Storage = Storage::new(2, 4);

/// The nodes and bytes that a term of degree $k \ge 2$ adds to its
/// coefficient, besides the variable name and the bit length of $k$: the
/// symbol, the exponent, the power and the product, the bit length of the
/// denominator 1 and the 3 bytes of the exponent written as the rational
/// $k / 1$, and the operators of the power and the product.
const POWER_EXTRA: Storage = Storage::new(4, 12);

/// The cost of one addition between two terms.
const ADDITION_COST: Storage = Storage::new(1, 4);

/// The terms of a polynomial in increasing degree, none with the
/// coefficient zero, and the measure of their storage cost.
#[derive(Clone)]
pub(super) struct PolynomialTerms<E> {
    /// The degrees, strictly increasing.
    degrees: Vec<u64>,
    /// The coefficient of each degree, none zero.
    coefficients: Vec<E>,
    /// The cost of the terms, without the variable name.
    measure: PolynomialMeasure,
}

/// The storage cost of the terms of a polynomial without the bytes of its
/// variable name: the nodes and the bytes, `None` when a sum does not fit in
/// a `u64`, and the number of terms of positive degree, each of which writes
/// the variable name once.
#[derive(Clone, Copy)]
struct PolynomialMeasure {
    nodes: Option<u64>,
    bytes: Option<u64>,
    named: u64,
}

impl<E> PolynomialTerms<E> {
    /// No terms: the zero polynomial.
    pub(super) const fn new() -> Self {
        Self {
            degrees: Vec::new(),
            coefficients: Vec::new(),
            measure: PolynomialMeasure {
                nodes: Some(0),
                bytes: Some(0),
                named: 0,
            },
        }
    }

    /// No terms, with room for `capacity` terms.
    pub(super) fn with_capacity(capacity: usize) -> Self {
        Self {
            degrees: Vec::with_capacity(capacity),
            coefficients: Vec::with_capacity(capacity),
            measure: PolynomialMeasure {
                nodes: Some(0),
                bytes: Some(0),
                named: 0,
            },
        }
    }

    /// The number of terms.
    pub(super) fn len(&self) -> usize {
        self.degrees.len()
    }

    /// Whether there is no term: the zero polynomial.
    pub(super) fn is_empty(&self) -> bool {
        self.degrees.is_empty()
    }

    /// The degrees, in increasing order.
    pub(super) fn degrees(&self) -> &[u64] {
        &self.degrees
    }

    /// The coefficients, in the order of the degrees.
    pub(super) fn coefficients(&self) -> &[E] {
        &self.coefficients
    }

    /// The degree and the coefficient of the term at `index`, or `None` past
    /// the last term.
    pub(super) fn term(&self, index: usize) -> Option<(u64, &E)> {
        match (self.degrees.get(index), self.coefficients.get(index)) {
            (Some(degree), Some(coefficient)) => Some((*degree, coefficient)),
            _ => None,
        }
    }

    /// The lowest degree, or `None` for no terms.
    pub(super) fn first_degree(&self) -> Option<u64> {
        if self.degrees.is_empty() {
            None
        } else {
            Some(self.degrees[0])
        }
    }

    /// The highest degree, the degree of the polynomial, or `None` for no
    /// terms.
    pub(super) fn last_degree(&self) -> Option<u64> {
        let length = self.degrees.len();
        if length == 0 {
            None
        } else {
            Some(self.degrees[length - 1])
        }
    }

    /// The storage cost of the polynomial for a variable name of
    /// `variable_length` bytes: the nodes and the bytes, `None` when the
    /// amount does not fit in a `u64`.
    pub(super) fn cost(&self, variable_length: u64) -> (Option<u64>, Option<u64>) {
        if self.degrees.is_empty() {
            return (Some(ZERO_COST.nodes), Some(ZERO_COST.bytes));
        }
        // A constant writes the variable name once, as every term of
        // positive degree does.
        let named = if self.measure.named == 0 {
            1
        } else {
            self.measure.named
        };
        let bytes = match named.checked_mul(variable_length) {
            Some(names) => add_option(self.measure.bytes, names),
            None => None,
        };
        (self.measure.nodes, bytes)
    }
}

impl<E> PolynomialTerms<E> {
    /// Appends the term `coefficient` $x^{\mathrm{degree}}$ of the coefficient
    /// ring `ring` and adds its cost to the measure, with the cost of the
    /// coefficient taken from `measure` of the ring. The caller has found
    /// `coefficient` not zero.
    ///
    /// # Errors
    ///
    /// As [`append_term`](PolynomialTerms::append_term).
    pub(super) fn push<K>(&mut self, ring: &K, degree: u64, coefficient: E) -> Result<()>
    where
        K: CoefficientRing<Element = E>,
    {
        let element = ring.measure(&coefficient);
        self.append_term(degree, coefficient, element)
    }

    /// Appends the term `coefficient` $x^{\mathrm{degree}}$ whose coefficient
    /// costs `element` and adds its cost to the measure. This is the only
    /// writer of the lists: it keeps the degrees strictly increasing.
    ///
    /// # Errors
    ///
    /// `Fault(Internal)` when `degree` is not above the last degree, a broken
    /// invariant of the caller; nothing is appended.
    fn append_term(&mut self, degree: u64, coefficient: E, element: Storage) -> Result<()> {
        let joined = match self.last_degree() {
            Some(last) => {
                if degree <= last {
                    return Err(internal("a term not above the last degree"));
                }
                true
            }
            None => false,
        };
        self.measure = self.measure.with_term(degree, element, joined);
        self.degrees.push(degree);
        self.coefficients.push(coefficient);
        Ok(())
    }
}

impl PolynomialMeasure {
    /// The measure with one more term of `degree`, whose coefficient costs
    /// `element`; `joined` when the term is added to earlier terms.
    fn with_term(self, degree: u64, element: Storage, joined: bool) -> Self {
        let own = term_cost(degree, element);
        let (nodes, bytes) = if joined {
            (
                add_option(own.0, ADDITION_COST.nodes),
                add_option(own.1, ADDITION_COST.bytes),
            )
        } else {
            own
        };
        let named = if degree > 0 {
            self.named.saturating_add(1)
        } else {
            self.named
        };
        Self {
            nodes: add_options(self.nodes, nodes),
            bytes: add_options(self.bytes, bytes),
            named,
        }
    }
}

/// The cost of a term of `degree` whose coefficient costs `element`, without
/// the variable name.
fn term_cost(degree: u64, element: Storage) -> (Option<u64>, Option<u64>) {
    match degree {
        0 => (Some(element.nodes), Some(element.bytes)),
        1 => (
            element.nodes.checked_add(LINEAR_EXTRA.nodes),
            element.bytes.checked_add(LINEAR_EXTRA.bytes),
        ),
        _ => (
            element.nodes.checked_add(POWER_EXTRA.nodes),
            add_option(
                element.bytes.checked_add(POWER_EXTRA.bytes),
                bit_length(degree),
            ),
        ),
    }
}

/// `total + value`, or `None` when `total` is `None` or the sum does not fit
/// in a `u64`.
const fn add_option(total: Option<u64>, value: u64) -> Option<u64> {
    match total {
        Some(total) => total.checked_add(value),
        None => None,
    }
}

/// `left + right`, or `None` when either is `None` or the sum does not fit in
/// a `u64`.
const fn add_options(left: Option<u64>, right: Option<u64>) -> Option<u64> {
    match right {
        Some(right) => add_option(left, right),
        None => None,
    }
}

/// The bit length of `value`: 0 for zero, otherwise
/// $\lfloor \log_2 v \rfloor + 1$.
const fn bit_length(value: u64) -> u64 {
    let mut rest = value;
    let mut bits = 0;
    while rest > 0 {
        rest >>= 1;
        bits += 1;
    }
    bits
}

/// Checks the terms `terms` of a polynomial whose variable has the name
/// `variable` against the limits of the context: its degree against
/// `max_exponent` and the width of `i64`, then its cost with
/// `check_storage` at scope `Value`, together with the open frames and the
/// reserved temporaries. Charges nothing.
///
/// # Errors
///
/// `ResourceLimit` with `LimitField::Exponent` for the degree, and with
/// `LimitField::Nodes` or `LimitField::StorageBytes` and the scope `Value`
/// for the cost, the nodes first; an amount that does not fit in a `u64`
/// exceeds every limit and is reported with `LimitAmount::Bound(u64::MAX)`.
pub(super) fn check<E>(
    terms: &PolynomialTerms<E>,
    variable: &str,
    context: &Context,
) -> Result<()> {
    check_last_degree(terms, context)?;
    let (nodes, bytes) = terms.cost(variable.len() as u64);
    admitted_cost(nodes, bytes, context)
}

/// Checks the degree of `terms`, if they have one, as [`check_degree`]
/// does; the zero polynomial has no degree and passes.
fn check_last_degree<E>(terms: &PolynomialTerms<E>, context: &Context) -> Result<()> {
    match terms.last_degree() {
        Some(degree) => check_degree(Some(degree), context),
        None => Ok(()),
    }
}

/// Checks a degree, or an exponent, against `max_exponent` and the width of
/// `i64`, whose smaller value is the effective bound; `None` is an amount
/// beyond `u64::MAX`, which exceeds every limit. Charges nothing.
pub(super) fn check_degree(degree: Option<u64>, context: &Context) -> Result<()> {
    context.check_width_at(LimitField::Exponent, DEGREE_WIDTH, degree, None)
}

/// Checks the cost of a new polynomial at scope `Value`, together with the
/// open frames and the reserved temporaries. A component that does not fit
/// in a `u64` exceeds every limit; the nodes are reported before the bytes.
fn admitted_cost(nodes: Option<u64>, bytes: Option<u64>, context: &Context) -> Result<()> {
    match nodes {
        None => Err(beyond_every_limit(LimitField::Nodes, context)),
        Some(nodes) => match bytes {
            None => {
                context.check_storage(Storage::new(nodes, 0), LimitScope::Value)?;
                Err(beyond_every_limit(LimitField::StorageBytes, context))
            }
            Some(bytes) => context.check_storage(Storage::new(nodes, bytes), LimitScope::Value),
        },
    }
}

/// The error of an amount of `field` that does not fit in a `u64`.
fn beyond_every_limit(field: LimitField, context: &Context) -> Error {
    match context.check_bound_at(field, None, None) {
        Err(error) => error,
        Ok(()) => internal("an amount beyond u64::MAX was admitted"),
    }
}

/// The fault of a broken internal invariant of the polynomials.
pub(super) fn internal(message: &str) -> Error {
    Error::new(FaultKind::Internal, None, message)
}

/// The writer of terms with a given cost, for the unit tests of polynomials.
#[cfg(test)]
mod test_writer {
    use super::PolynomialTerms;
    use crate::Result;
    use crate::context::Storage;

    impl<E> PolynomialTerms<E> {
        /// Appends the term `coefficient` $x^{\mathrm{degree}}$ whose
        /// coefficient costs `element`, for the unit tests, which reach
        /// amounts beyond `u64::MAX` with costs that no rational has.
        ///
        /// # Errors
        ///
        /// As [`append_term`](PolynomialTerms::append_term).
        pub(in crate::polynomial) fn push_with_cost(
            &mut self,
            degree: u64,
            coefficient: E,
            element: Storage,
        ) -> Result<()> {
            self.append_term(degree, coefficient, element)
        }
    }
}
