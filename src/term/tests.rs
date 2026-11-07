//! Unit tests of the term core that need its private parts: the reserved
//! call node, the measures cached in the nodes against a count written here,
//! the structural invariants of canonical forms on fixed terms, sharing
//! without an intern table, drop with shared subterms, and the scaling and
//! the primitive parts of sums.

use std::cmp::Ordering;
use std::rc::Rc;

use super::exponent::mergeable;
use super::node::{CallClass, TermShape, is_one};
use super::*;
use crate::context::CancelFlag;
use crate::{ErrorKind, FaultKind, Limits};

fn context() -> Context {
    Context::new(Limits::new(), CancelFlag::new())
}

fn symbol(name: &str, c: &mut Context) -> Term {
    Term::symbol(name, c).unwrap()
}

fn integer(value: i64, c: &mut Context) -> Term {
    Term::number(Rational::from(value), c).unwrap()
}

fn show(term: &Term, c: &mut Context) -> String {
    term.display(c).unwrap()
}

fn call(name: &str, class: CallClass, arguments: &[Term], c: &mut Context) -> Term {
    reserved_call(name, class, arguments, c).unwrap()
}

fn order(left: &Term, right: &Term, c: &mut Context) -> Ordering {
    left.compare(right, c).unwrap()
}

// ---------------------------------------------------------------------------
// The reserved call node

// A call has rank 3: after numbers and symbols, before powers, products and
// sums.
#[test]
fn calls_sort_after_symbols_and_before_powers() {
    let c = &mut context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let seven = integer(7, c);
    let f = call("f", CallClass::Registered, std::slice::from_ref(&x), c);
    let square = x.power(2, c).unwrap();
    let product = Term::product(&[x.clone(), y.clone()], c).unwrap();
    let sum = Term::sum(&[x.clone(), y.clone()], c).unwrap();
    let chain = [seven, y, f.clone(), square, product, sum];
    let mut index = 0;
    while index + 1 < chain.len() {
        assert_eq!(order(&chain[index], &chain[index + 1], c), Ordering::Less);
        assert_eq!(
            order(&chain[index + 1], &chain[index], c),
            Ordering::Greater
        );
        index += 1;
    }
    assert_eq!(f.kind(), TermKind::Call);
    assert_eq!(f.kind().rank(), 3);
}

// Calls compare by the bytes of the head name, the head class, the arguments
// one by one and the number of arguments, in that order.
#[test]
fn calls_order_by_head_name_class_arguments_and_count() {
    let c = &mut context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let f_x = call("f", CallClass::Formal, std::slice::from_ref(&x), c);
    let g_x = call("g", CallClass::Registered, std::slice::from_ref(&x), c);
    let f_y = call("f", CallClass::Formal, std::slice::from_ref(&y), c);
    let registered = call("f", CallClass::Registered, std::slice::from_ref(&y), c);
    let f_x_y = call("f", CallClass::Formal, &[x.clone(), y.clone()], c);
    // The name decides before the arguments: f(y) < g(x).
    assert_eq!(order(&f_y, &g_x, c), Ordering::Less);
    // Then the class: Registered before Formal.
    assert_eq!(order(&registered, &f_y, c), Ordering::Less);
    // Then the arguments one by one, then their number.
    assert_eq!(order(&f_x, &f_y, c), Ordering::Less);
    assert_eq!(order(&f_x, &f_x_y, c), Ordering::Less);
    assert_eq!(order(&f_x_y, &f_y, c), Ordering::Less);
    let again = call("f", CallClass::Formal, &[x.clone(), y.clone()], c);
    assert!(f_x_y.equals(&again, c).unwrap());
}

// A call is an atom of sums, products and powers: equal calls merge as
// bases and as cores, and its arguments keep their given order.
#[test]
fn calls_are_atoms_of_sums_products_and_powers() {
    let c = &mut context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let f = call("f", CallClass::Formal, std::slice::from_ref(&x), c);
    let again = call("f", CallClass::Formal, std::slice::from_ref(&x), c);
    let square = Term::product(&[f.clone(), again.clone()], c).unwrap();
    assert_eq!(show(&square, c), "f(x)^2");
    let two = integer(2, c);
    let double = Term::product(&[two, f.clone()], c).unwrap();
    let triple = Term::sum(&[double, again], c).unwrap();
    assert_eq!(show(&triple, c), "3*f(x)");
    let inverse = f.power(-1, c).unwrap();
    assert_eq!(show(&inverse.power(-1, c).unwrap(), c), "(f(x)^(-1))^(-1)");
    let sum = Term::sum(&[y.clone(), x.clone()], c).unwrap();
    let swapped = call("g", CallClass::Formal, &[y.clone(), x.clone()], c);
    let nested = call("g", CallClass::Formal, &[sum, y], c);
    assert_eq!(show(&swapped, c), "g(y, x)");
    assert_eq!(show(&nested, c), "g(x + y, y)");
    // A negative power inside an argument is a negative base of the call.
    let hidden = call("h", CallClass::Formal, &[x.power(-1, c).unwrap()], c);
    assert!(hidden.has_negative_power());
    let bases = hidden.negative_bases(c).unwrap();
    assert_eq!(bases.len(), 1);
    assert!(bases[0].equals(&x, c).unwrap());
}

// The provisional cost of the reserved call: its head name, its arguments
// and 4 bytes per argument.
#[test]
fn the_cost_of_a_call_counts_its_name_and_arguments() {
    let c = &mut context();
    let x = symbol("x", c);
    let y = symbol("yy", c);
    let f = call("fn", CallClass::Formal, &[x, y], c);
    assert_eq!(f.storage(), Storage::new(3, 2 + 1 + 2 + 8));
}

// ---------------------------------------------------------------------------
// Sharing without an intern table

// Two equal terms built apart are two nodes: the constructors look nothing
// up, so equality is structural. A clone shares its node, and the
// comparison charges the same for a shared and a separate node.
#[test]
fn equal_terms_built_apart_are_separate_nodes() {
    let c = &mut context();
    let left = {
        let x = symbol("x", c);
        let y = symbol("y", c);
        Term::sum(&[x, y], c).unwrap()
    };
    let right = {
        let y = symbol("y", c);
        let x = symbol("x", c);
        Term::sum(&[y, x], c).unwrap()
    };
    assert!(left.equals(&right, c).unwrap());
    assert!(!Rc::ptr_eq(&left.0, &right.0));
    let copy = left.clone();
    assert!(Rc::ptr_eq(&left.0, &copy.0));
    let before = c.work_used();
    left.compare(&copy, c).unwrap();
    let shared = c.work_used() - before;
    let before = c.work_used();
    left.compare(&right, c).unwrap();
    assert_eq!(c.work_used() - before, shared);
}

// Dropping a term frees the nodes it owns alone and leaves shared subterms
// intact.
#[test]
fn dropping_a_term_keeps_its_shared_subterms() {
    let c = &mut context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let inner = Term::sum(&[x.clone(), y.clone()], c).unwrap();
    let mut outer = inner.clone();
    let mut step = 0;
    while step < 20 {
        outer = Term::product(&[x.clone(), outer], c).unwrap();
        outer = Term::sum(&[outer, y.clone()], c).unwrap();
        step += 1;
    }
    assert_eq!(Rc::strong_count(&inner.0), 2);
    drop(outer);
    assert_eq!(Rc::strong_count(&inner.0), 1);
    assert_eq!(show(&inner, c), "x + y");
    assert_eq!(Rc::strong_count(&x.0), 2);
}

// ---------------------------------------------------------------------------
// Cached measures

/// The bit length of a value.
fn bit_length(value: u64) -> u64 {
    u64::from(u64::BITS - value.leading_zeros())
}

/// The bytes of a rational $n/d$, $\lvert n \rvert + \lvert d \rvert + 3$.
fn rational_bytes(value: &Rational) -> u64 {
    value.numerator().bits() + value.denominator().bits() + 3
}

/// The size, depth, bytes and negative flag of a term, counted from its
/// children by the canonical binary rendering of the contract.
fn recount(term: &Term) -> (u64, u64, u64, bool) {
    let mut size = 1;
    let mut depth = 0;
    let mut bytes = 0;
    let mut negative = false;
    for child in term.children() {
        let (s, d, b, n) = recount(child);
        size += s;
        depth = depth.max(d);
        bytes += b;
        negative |= n;
    }
    let children = term.children().len() as u64;
    let own = match &term.0.shape {
        TermShape::Number(value) => rational_bytes(value),
        TermShape::Symbol(name) => name.len() as u64,
        TermShape::Call(head) => head.name.len() as u64 + 4 * children,
        TermShape::Power(k) => {
            negative |= *k < 0;
            // The exponent as the rational k/1, and one binary power.
            bit_length(k.unsigned_abs()) + 1 + 3 + 4
        }
        TermShape::Product(coefficient) => {
            let operands = children + u64::from(!is_one(coefficient));
            let written = if is_one(coefficient) {
                0
            } else {
                rational_bytes(coefficient)
            };
            written + 4 * (operands - 1)
        }
        TermShape::Sum(constant, coefficients) => {
            let operands = children + u64::from(!constant.is_zero());
            let mut written = if constant.is_zero() {
                0
            } else {
                rational_bytes(constant)
            };
            for coefficient in coefficients {
                if !is_one(coefficient) {
                    written += rational_bytes(coefficient) + 4;
                }
            }
            written + 4 * (operands - 1)
        }
    };
    (size, depth + 1, bytes + own, negative)
}

/// A set of canonical terms of every kind and witness shape.
fn samples(c: &mut Context) -> Vec<Term> {
    let x = symbol("x", c);
    let y = symbol("long_name", c);
    let half = Rational::from(1).divide(&Rational::from(2), c).unwrap();
    let half = Term::number(half, c).unwrap();
    let minus = integer(-3, c);
    let zero = integer(0, c);
    let inverse = x.power(-1, c).unwrap();
    let sum = Term::sum(&[x.clone(), y.clone(), half.clone()], c).unwrap();
    let scaled = Term::product(&[minus.clone(), sum.clone()], c).unwrap();
    let factor = Term::product(&[scaled.clone(), y.clone()], c).unwrap();
    let base = scaled.power(-3, c).unwrap();
    let witness = inverse.power(0, c).unwrap();
    let zero_product = Term::product(&[zero, inverse.clone()], c).unwrap();
    let negated = Term::product(&[minus.clone(), inverse.clone()], c).unwrap();
    let doubled = Term::product(&[integer(2, c), inverse.clone()], c).unwrap();
    let cancelled = Term::sum(&[inverse.clone(), negated, doubled, y.clone()], c).unwrap();
    let cube = x.power(3, c).unwrap();
    let mixed = Term::product(&[cube, inverse.clone(), y.clone()], c).unwrap();
    let nested = inverse.power(-2, c).unwrap();
    let witness_product = Term::product(&[witness.clone(), y.clone(), half.clone()], c).unwrap();
    let numerator = Rational::from(7).power(300, c).unwrap();
    let denominator = Rational::from(3).power(100, c).unwrap();
    let big = Term::number(numerator.divide(&denominator, c).unwrap(), c).unwrap();
    let parts = [
        scaled.clone(),
        mixed.clone(),
        witness_product.clone(),
        big.clone(),
    ];
    let deep = Term::sum(&parts, c).unwrap();
    let power_of_sum = sum.power(-7, c).unwrap();
    let f = call("f", CallClass::Formal, &[sum.clone(), inverse.clone()], c);
    let negated_inverse = inverse.negate(c).unwrap();
    let only_witness = Term::sum(&[inverse.clone(), negated_inverse, minus.clone()], c).unwrap();
    let witness_factor = Term::product(&[only_witness.clone(), x.clone()], c).unwrap();
    vec![
        x,
        y,
        half,
        minus,
        inverse,
        sum,
        scaled,
        witness,
        zero_product,
        cancelled,
        mixed,
        nested,
        witness_product,
        big,
        deep,
        power_of_sum,
        f,
        factor,
        base,
        only_witness,
        witness_factor,
    ]
}

// The tree size, the depth, the logical bytes and the negative flag that a
// node caches are those that a recursive count gives.
#[test]
fn cached_measures_match_a_recursive_count() {
    let c = &mut context();
    for term in samples(c) {
        let (size, depth, bytes, negative) = recount(&term);
        let text = show(&term, c);
        assert_eq!(term.size(), size, "{text}");
        assert_eq!(term.depth(), depth, "{text}");
        assert_eq!(term.storage(), Storage::new(size, bytes), "{text}");
        assert_eq!(term.has_negative_power(), negative, "{text}");
    }
}

// ---------------------------------------------------------------------------
// Structural invariants

/// The key of a factor: its base and the sign of its exponent for a power,
/// the factor itself otherwise.
fn factor_key(factor: &Term) -> (Term, bool) {
    match factor.as_power() {
        Some((base, k)) => (base.clone(), k < 0),
        None => (factor.clone(), false),
    }
}

fn is_reciprocal(term: &Term) -> bool {
    matches!(term.as_power(), Some((_, -1)))
}

/// Whether the sum `term` is primitive: the coefficient of its first
/// monomial that is not 0, or its constant when there is none, is 1.
fn is_primitive(term: &Term) -> bool {
    let (constant, coefficients, _) = term.as_sum().unwrap();
    let content = coefficients
        .iter()
        .find(|coefficient| !coefficient.is_zero())
        .unwrap_or(constant);
    is_one(content)
}

/// Checks the local rules of the canonical form at every node of `term`.
fn check_invariants(term: &Term, c: &mut Context) -> std::result::Result<(), String> {
    let mut stack = vec![term.clone()];
    while let Some(node) = stack.pop() {
        check_node(&node, c)?;
        stack.extend(node.children().iter().cloned());
    }
    Ok(())
}

fn check_power(base: &Term, k: i64) -> std::result::Result<(), String> {
    if matches!(base.kind(), TermKind::Number | TermKind::Product) {
        return Err("a power of a number or a product".into());
    }
    if base.kind() == TermKind::Sum && !is_primitive(base) {
        return Err("a power of a sum that is not primitive".into());
    }
    if k == 1 {
        return Err("the exponent 1".into());
    }
    if k == 0 && !is_reciprocal(base) {
        return Err("the exponent 0 outside a witness".into());
    }
    if let Some((_, j)) = base.as_power()
        && mergeable(j, k)
    {
        return Err("a power of a power that merges".into());
    }
    Ok(())
}

fn check_product(
    coefficient: &Rational,
    factors: &[Term],
    c: &mut Context,
) -> std::result::Result<(), String> {
    if factors.is_empty() || (is_one(coefficient) && factors.len() == 1) {
        return Err("a product without factors, or one factor and 1".into());
    }
    if factors.len() == 1 && factors[0].kind() == TermKind::Sum {
        return Err("a product whose only factor is a sum".into());
    }
    for (index, factor) in factors.iter().enumerate() {
        if matches!(factor.kind(), TermKind::Number | TermKind::Product) {
            return Err("a number or a product as a factor".into());
        }
        if factor.kind() == TermKind::Sum && !is_primitive(factor) {
            return Err("a sum factor that is not primitive".into());
        }
        if coefficient.is_zero() && !is_reciprocal(factor) {
            return Err("a zero product with a factor that is not a reciprocal".into());
        }
        if index > 0 {
            let (a, s) = factor_key(&factors[index - 1]);
            let (b, t) = factor_key(factor);
            let by_base = a.compare(&b, c).unwrap();
            if by_base == Ordering::Greater || (by_base == Ordering::Equal && (s || !t)) {
                return Err("factor keys not strictly increasing".into());
            }
        }
    }
    Ok(())
}

fn check_sum(
    constant: &Rational,
    coefficients: &[Rational],
    cores: &[Term],
    c: &mut Context,
) -> std::result::Result<(), String> {
    let operands = cores.len() + usize::from(!constant.is_zero());
    if operands < 2 || coefficients.len() != cores.len() {
        return Err("a sum of fewer than two operands".into());
    }
    let mut zeros = 0;
    for (index, core) in cores.iter().enumerate() {
        if core.kind() == TermKind::Number {
            return Err("a number as a core".into());
        }
        if core.kind() == TermKind::Sum {
            return Err("a sum as a core".into());
        }
        if let Some((factor, _)) = core.as_product()
            && !is_one(factor)
        {
            return Err("a core with a coefficient".into());
        }
        if coefficients[index].is_zero() {
            zeros += 1;
        }
        if index > 0 && cores[index - 1].compare(core, c).unwrap() != Ordering::Less {
            return Err("cores not strictly increasing".into());
        }
    }
    if zeros > 1 {
        return Err("more than one witness monomial".into());
    }
    Ok(())
}

fn check_node(term: &Term, c: &mut Context) -> std::result::Result<(), String> {
    if let Some((base, k)) = term.as_power() {
        return check_power(base, k);
    }
    if let Some((coefficient, factors)) = term.as_product() {
        return check_product(coefficient, factors, c);
    }
    if let Some((constant, coefficients, cores)) = term.as_sum() {
        return check_sum(constant, coefficients, cores, c);
    }
    if matches!(term.kind(), TermKind::Number | TermKind::Symbol) && !term.children().is_empty() {
        return Err("a leaf with children".into());
    }
    Ok(())
}

// Every node of the sample terms keeps the local rules of the canonical
// form.
#[test]
fn sample_terms_keep_the_local_rules_of_the_canonical_form() {
    let c = &mut context();
    for term in samples(c) {
        let text = show(&term, c);
        check_invariants(&term, c).unwrap_or_else(|error| panic!("{error}: {text}"));
    }
}

// A broken internal invariant is an `Internal` fault, never a panic: a
// symbol has no base, so asking for one fails; a symbol has no parts of a
// sum, so it has no content; a sum has no content 0, neither when its first
// two coefficients are 0 nor when its only coefficient and its constant are,
// where the inverse of the content would otherwise fail with
// `DivisionByZero`, and it is never scaled by 0; and a product whose only
// factor is a sum is not canonical, so a sum that meets one reports it.
#[test]
fn a_broken_invariant_is_an_internal_fault() {
    let c = &mut context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let error = node::first_child(&x).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Internal));
    let error = sum::primitive(&x, c).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Internal));
    let zeros = vec![Rational::from(0), Rational::from(0)];
    let shape = TermShape::Sum(Rational::from(0), zeros);
    let broken = node::make(shape, vec![x.clone(), y.clone()], c).unwrap();
    let error = sum::primitive(&broken, c).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Internal));
    let inverse = x.power(-1, c).unwrap();
    let shape = TermShape::Sum(Rational::from(0), vec![Rational::from(0)]);
    let broken = node::make(shape, vec![inverse], c).unwrap();
    let error = sum::primitive(&broken, c).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Internal));
    let pair = Term::sum(&[x.clone(), y], c).unwrap();
    let error = sum::scaled(&Rational::from(0), &pair, c).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Internal));
    let broken = node::make(TermShape::Product(Rational::from(2)), vec![pair], c).unwrap();
    let error = Term::sum(&[broken, x], c).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Internal));
}

// ---------------------------------------------------------------------------
// Scaling and primitive parts of sums

// Scaling a sum multiplies its constant and its coefficients and keeps its
// cores, their order and its witness monomial; the primitive part divides
// by the content, the first coefficient that is not 0, and a primitive sum
// is its own primitive part.
#[test]
fn scaling_keeps_the_cores_and_the_primitive_part_has_the_content_1() {
    let c = &mut context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let inverse = x.power(-1, c).unwrap();
    let parts = [
        integer(3, c),
        Term::product(&[integer(2, c), y.clone()], c).unwrap(),
        inverse.clone(),
        inverse.negate(c).unwrap(),
    ];
    let total = Term::sum(&parts, c).unwrap();
    assert_eq!(show(&total, c), "3 + 2*y + 0*x^(-1)");
    let scaled = sum::scaled(&Rational::from(-2), &total, c).unwrap();
    assert_eq!(show(&scaled, c), "-6 - 4*y + 0*x^(-1)");
    check_invariants(&scaled, c).unwrap();
    let (content, part) = sum::primitive(&total, c).unwrap();
    assert_eq!(content, Rational::from(2));
    assert_eq!(show(&part, c), "3/2 + y + 0*x^(-1)");
    assert!(is_primitive(&part));
    let (content, same) = sum::primitive(&part, c).unwrap();
    assert!(is_one(&content));
    assert!(Rc::ptr_eq(&same.0, &part.0));
    let mut index = 0;
    while index < total.children().len() {
        let (core, scaled_core) = (&total.children()[index], &scaled.children()[index]);
        assert!(Rc::ptr_eq(&core.0, &scaled_core.0));
        index += 1;
    }
    // A sum whose only monomial is the witness has its constant as its
    // content.
    let only = Term::sum(
        &[inverse.clone(), inverse.negate(c).unwrap(), integer(-4, c)],
        c,
    )
    .unwrap();
    let (content, part) = sum::primitive(&only, c).unwrap();
    assert_eq!(content, Rational::from(-4));
    assert_eq!(show(&part, c), "1 + 0*x^(-1)");
}
