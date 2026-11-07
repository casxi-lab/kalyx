//! Unit tests of the polynomials that need their private parts: the measure
//! of the storage cost against a count written here, its amounts beyond
//! `u64::MAX`, the width of degrees, the highest bit of an exponent and the
//! degree guard of the conversion back to terms.

use super::arithmetic::highest_bit;
use super::conversion::variable_power;
use super::terms::{self, DEGREE_WIDTH, PolynomialTerms};
use super::*;
use crate::context::CancelFlag;
use crate::number::Rational;
use crate::{ErrorKind, FaultKind, LimitAmount, LimitField, LimitId, LimitScope, Limits};

fn context(limits: Limits) -> Context {
    Context::new(limits, CancelFlag::new())
}

/// The bit length of `value`, by repeated halving.
fn bits(value: u64) -> u64 {
    let mut rest = value;
    let mut count = 0;
    while rest > 0 {
        rest /= 2;
        count += 1;
    }
    count
}

/// The cost of the terms `(degree, coefficient)` for a variable name of
/// `length` bytes, counted here from the formula of the contract.
fn recount(terms: &[(u64, Rational)], length: u64) -> Storage {
    if terms.is_empty() {
        return Storage::new(1, 4);
    }
    let mut nodes = 0;
    let mut bytes = 0;
    let mut positive = false;
    for (degree, coefficient) in terms {
        let rb = coefficient.numerator().bits() + coefficient.denominator().bits() + 3;
        match degree {
            0 => {
                nodes += 1;
                bytes += rb;
            }
            1 => {
                nodes += 3;
                bytes += rb + length + 4;
                positive = true;
            }
            k => {
                nodes += 5;
                bytes += rb + length + bits(*k) + 12;
                positive = true;
            }
        }
    }
    nodes += terms.len() as u64 - 1;
    bytes += 4 * (terms.len() as u64 - 1);
    if !positive {
        bytes += length;
    }
    Storage::new(nodes, bytes)
}

// The measure that a list of terms keeps as it grows is the cost that the
// formula gives, for every shape: zero, constants, terms of degree 1 and
// of higher degree, and every length of the variable name.
#[test]
fn the_measure_is_the_storage_formula() {
    let mut state: u64 = 0x5EED_0000_0000_00A1;
    let mut next = || {
        state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    };
    let c = &mut context(Limits::new());
    for case in 0..1_000 {
        let count = (next() % 6) as usize;
        let mut degree = next() % 3;
        let mut terms = Vec::new();
        for _ in 0..count {
            let numerator = (next() % 2_000) as i64 - 1_000;
            let numerator = if numerator == 0 { 7 } else { numerator };
            let denominator = (next() % 50) as i64 + 1;
            let value = Rational::new(
                crate::number::Integer::from(numerator),
                crate::number::Integer::from(denominator),
                c,
            )
            .unwrap();
            terms.push((degree, value));
            degree += 1 + next() % 800;
        }
        let mut list = PolynomialTerms::new();
        for (degree, value) in &terms {
            list.push(&Rationals, *degree, value.clone()).unwrap();
        }
        for name in ["x", "abc", "a_long_variable_name"] {
            let length = name.len() as u64;
            let (nodes, bytes) = list.cost(length);
            let expected = recount(&terms, length);
            assert_eq!(
                (nodes, bytes),
                (Some(expected.nodes), Some(expected.bytes)),
                "case {case}"
            );
            let ring = PolynomialRing::new(Rationals, name, c).unwrap();
            let polynomial = arithmetic::admit(&ring, list.clone(), c).unwrap();
            assert_eq!(ring.storage(&polynomial), expected, "case {case}");
        }
    }
}

// A measure beyond `u64::MAX` exceeds every limit, also `u64::MAX`: the
// nodes are reported before the bytes, with the amount
// `LimitAmount::Bound(u64::MAX)` and the scope `Value`, and the storage
// that the ring reports stops at `u64::MAX`.
#[test]
fn a_measure_beyond_u64_max_exceeds_every_limit() {
    let unlimited = Limits::new()
        .with_max_nodes(u64::MAX)
        .with_max_storage_bytes(u64::MAX);
    let c = &mut context(unlimited);
    let ring = PolynomialRing::new(Rationals, "x", c).unwrap();
    let check = |list: &PolynomialTerms<()>, c: &Context| terms::check(list, "x", c);

    let mut nodes = PolynomialTerms::new();
    nodes
        .push_with_cost(0, (), Storage::new(u64::MAX, 1))
        .unwrap();
    assert!(check(&nodes, c).is_ok());
    nodes.push_with_cost(1, (), Storage::new(1, 1)).unwrap();
    let error = check(&nodes, c).unwrap_err();
    let exceeded = error.exceeded().unwrap();
    assert_eq!(exceeded.id(), &LimitId::Field(LimitField::Nodes));
    assert_eq!(exceeded.amount(), LimitAmount::Bound(u64::MAX));
    assert_eq!(exceeded.scope(), Some(LimitScope::Value));

    let mut bytes = PolynomialTerms::new();
    bytes
        .push_with_cost(0, (), Storage::new(1, u64::MAX - 1))
        .unwrap();
    assert!(check(&bytes, c).is_ok());
    bytes.push_with_cost(2, (), Storage::new(1, 1)).unwrap();
    let error = check(&bytes, c).unwrap_err();
    let exceeded = error.exceeded().unwrap();
    assert_eq!(exceeded.id(), &LimitId::Field(LimitField::StorageBytes));
    assert_eq!(exceeded.amount(), LimitAmount::Bound(u64::MAX));
    // The variable name alone can take the bytes beyond `u64::MAX`.
    let mut named = PolynomialTerms::new();
    named
        .push_with_cost(0, (), Storage::new(1, u64::MAX))
        .unwrap();
    assert_eq!(named.cost(0), (Some(1), Some(u64::MAX)));
    assert_eq!(named.cost(1), (Some(1), None));
    // Both beyond: the nodes are reported.
    nodes
        .push_with_cost(3, (), Storage::new(1, u64::MAX))
        .unwrap();
    let error = check(&nodes, c).unwrap_err();
    assert_eq!(
        error.exceeded().unwrap().id(),
        &LimitId::Field(LimitField::Nodes)
    );
    // Nodes within `u64::MAX` are checked before bytes beyond it: within
    // the limit, the bytes are reported; beyond it, the nodes.
    let c = &mut context(Limits::new());
    let error = check(&bytes, c).unwrap_err();
    let exceeded = error.exceeded().unwrap();
    assert_eq!(exceeded.id(), &LimitId::Field(LimitField::StorageBytes));
    assert_eq!(exceeded.amount(), LimitAmount::Bound(u64::MAX));
    let mut crowded = PolynomialTerms::new();
    crowded
        .push_with_cost(0, (), Storage::new(9_000, u64::MAX))
        .unwrap();
    crowded.push_with_cost(1, (), Storage::new(1, 1)).unwrap();
    let error = check(&crowded, c).unwrap_err();
    let exceeded = error.exceeded().unwrap();
    assert_eq!(exceeded.id(), &LimitId::Field(LimitField::Nodes));
    assert_eq!(exceeded.amount(), LimitAmount::Required(9_000 + 3 + 1));
    // The storage that the ring reports is the measure with the variable
    // name, and an amount beyond `u64::MAX` stops at `u64::MAX`. A ring
    // takes only rationals, whose measure cannot get there, so the
    // saturation is checked on its own.
    let mut constant = PolynomialTerms::new();
    constant.push(&Rationals, 0, Rational::from(1_i64)).unwrap();
    let polynomial = Polynomial { terms: constant };
    assert_eq!(ring.storage(&polynomial), Storage::new(1, 5 + 1));
    assert_eq!(saturated(None), u64::MAX);
    assert_eq!(saturated(Some(6)), 6);
    assert_eq!(saturated(Some(u64::MAX)), u64::MAX);
}

// Degrees are bounded by `max_exponent` and by the width of `i64`, whose
// smaller value is the effective bound that a `ResourceLimit` reports.
#[test]
fn degrees_are_bounded_by_the_width_of_i64() {
    let c = &mut context(Limits::new().with_max_exponent(u64::MAX));
    assert!(terms::check_degree(Some(DEGREE_WIDTH), c).is_ok());
    let error = terms::check_degree(Some(DEGREE_WIDTH + 1), c).unwrap_err();
    let exceeded = error.exceeded().unwrap();
    assert_eq!(exceeded.id(), &LimitId::Field(LimitField::Exponent));
    assert_eq!(exceeded.allowed(), DEGREE_WIDTH);
    assert_eq!(exceeded.amount(), LimitAmount::Required(DEGREE_WIDTH + 1));
    let error = terms::check_degree(None, c).unwrap_err();
    assert_eq!(
        error.exceeded().unwrap().amount(),
        LimitAmount::Bound(u64::MAX)
    );
    let mut list = PolynomialTerms::new();
    list.push(&Rationals, DEGREE_WIDTH + 1, Rational::from(1_i64))
        .unwrap();
    let error = terms::check(&list, "x", c).unwrap_err();
    assert_eq!(
        error.exceeded().unwrap().id(),
        &LimitId::Field(LimitField::Exponent)
    );
}

// The highest bit of an exponent, from which a power starts.
#[test]
fn the_highest_bit_of_an_exponent() {
    for (value, bit) in [
        (1, 1),
        (2, 2),
        (3, 2),
        (5, 4),
        (4_096, 4_096),
        (4_097, 4_096),
        (u64::MAX, 1 << 63),
    ] {
        assert_eq!(highest_bit(value), bit, "{value}");
    }
}

// A degree beyond the width of `i64` never reaches a term: the conversion
// back reports it as a broken invariant, since every admitted polynomial
// has a degree within the width.
#[test]
fn a_degree_beyond_the_width_of_i64_is_an_internal_fault() {
    let c = &mut context(Limits::new());
    let x = Term::symbol("x", c).unwrap();
    let error = variable_power(&x, DEGREE_WIDTH + 1, c).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Internal));
    let same = variable_power(&x, 1, c).unwrap();
    assert!(same.equals(&x, c).unwrap());
}

// The only writer of a list of terms keeps the degrees strictly increasing:
// a term at or below the last degree is a broken invariant of its caller,
// and nothing is appended.
#[test]
fn a_term_not_above_the_last_degree_is_an_internal_fault() {
    let mut list = PolynomialTerms::new();
    list.push(&Rationals, 2, Rational::from(3_i64)).unwrap();
    for degree in [0, 1, 2] {
        let error = list
            .push(&Rationals, degree, Rational::from(5_i64))
            .unwrap_err();
        assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Internal));
    }
    assert_eq!(list.degrees(), &[2]);
    // rb(3) = 2 + 1 + 3.
    assert_eq!(list.cost(1), (Some(5), Some(6 + 1 + 2 + 12)));
    list.push(&Rationals, 3, Rational::from(5_i64)).unwrap();
    assert_eq!(list.degrees(), &[2, 3]);
}
