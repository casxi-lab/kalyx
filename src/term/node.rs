//! The node of a term: its shape, its children and the measures cached in
//! it, the checks that come before a node is allocated, and the iterative
//! drop.
//!
//! Every node of the library is built here, by [`make`], [`make_symbol`] or
//! [`number`], and only after the caller has made its shape and children
//! canonical. Before the allocation, the new depth is compared with
//! `max_depth`, and the cost of the new term, its tree size and its logical
//! bytes, is checked with `check_storage` at scope `Value`; only then is the
//! node charged and allocated.

use std::rc::Rc;

use crate::context::{Storage, StorageCost};
use crate::number::Rational;
use crate::{Context, Error, FaultKind, LimitField, LimitScope, Result};

use super::Term;
use super::exponent;

/// The shape of a node, with the data that the node holds itself. The
/// children of the node are kept apart, in [`TermNode::children`].
pub(super) enum TermShape {
    /// An exact rational number, without children.
    Number(Rational),
    /// A symbol, by its name, without children.
    Symbol(Box<str>),
    /// A call of a function, reserved: no constructor of this release builds
    /// one. The children are the arguments, in their given order.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "the call node is reserved; only the tests of the term core build one"
        )
    )]
    Call(CallHead),
    /// An integer power with this exponent; the only child is the base.
    Power(i64),
    /// A product with this coefficient; the children are the factors.
    Product(Rational),
    /// A sum with this constant and one coefficient per monomial; the
    /// children are the cores of the monomials, in the same order.
    Sum(Rational, Vec<Rational>),
}

/// The head of a reserved call node: the name of the function and its class.
pub(super) struct CallHead {
    pub(super) name: Box<str>,
    pub(super) class: CallClass,
}

/// What the head of a call names. Calls of one name order `Registered`
/// before `Formal`.
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "the call node is reserved; only the tests of the term core build one"
    )
)]
#[non_exhaustive]
#[derive(Clone, Copy)]
pub(super) enum CallClass {
    /// A function of the function registry.
    Registered,
    /// A formal function symbol, such as an unknown function $f$.
    Formal,
}

/// One node of a term. A node never changes after it is built.
pub(super) struct TermNode {
    /// The shape of the node and the data it holds itself.
    pub(super) shape: TermShape,
    /// The children, as the shape describes them.
    pub(super) children: Vec<Term>,
    /// The tree size: this node and the tree sizes of its children, so a
    /// shared subterm counts once for each occurrence.
    pub(super) size: u64,
    /// One more than the largest depth of the children; 1 for a leaf.
    pub(super) depth: u64,
    /// The logical bytes of the term, by the term formula of the contract.
    pub(super) bytes: u64,
    /// Whether the term holds a power with a negative exponent, this node
    /// included.
    pub(super) negative: bool,
}

/// The measures of a node that passed its checks.
#[derive(Clone, Copy)]
struct NodeMeasure {
    size: u64,
    depth: u64,
    bytes: u64,
    negative: bool,
}

/// The sums over the children of a node: their tree sizes and logical bytes,
/// `None` when a sum does not fit in a `u64`, their largest depth and
/// whether any of them holds a negative power.
struct ChildTotals {
    size: Option<u64>,
    bytes: Option<u64>,
    depth: u64,
    negative: bool,
}

impl Drop for TermNode {
    /// Releases the children through a stack of its own: a child that this
    /// node owns alone gives its children to the stack before it is freed,
    /// so no drop recurses, whatever the depth of the term.
    fn drop(&mut self) {
        let mut stack = std::mem::take(&mut self.children);
        while let Some(term) = stack.pop() {
            release(term, &mut stack);
        }
    }
}

/// Frees `term` when it is the last handle of its node, after moving the
/// children of the node onto `stack`; otherwise only drops the handle.
fn release(term: Term, stack: &mut Vec<Term>) {
    match Rc::try_unwrap(term.0) {
        Ok(mut node) => stack.append(&mut node.children),
        Err(_shared) => {}
    }
}

/// The node of `shape` over `children`, which the caller made canonical.
///
/// Compares the new depth with `max_depth`, then checks the cost of the new
/// term with `check_storage` at scope `Value`, then charges one unit and one
/// more per child, and only then allocates: a node that a check rejects is
/// not charged.
pub(super) fn make(shape: TermShape, children: Vec<Term>, context: &mut Context) -> Result<Term> {
    let own = shape_bytes(&shape, children.len());
    let negative = is_negative_power(&shape);
    let measure = admit(own, negative, &children, context)?;
    context.charge(node_charge(children.len()))?;
    Ok(allocate(shape, children, measure))
}

/// The symbol node of `name`, which the caller validated: checks as
/// [`make`] does, charges one unit and one more per byte of the name, and
/// only then copies the name.
pub(super) fn make_symbol(name: &str, context: &mut Context) -> Result<Term> {
    let length = name.len() as u64;
    let measure = admit(Some(length), false, &[], context)?;
    context.charge(length.saturating_add(1))?;
    Ok(allocate(
        TermShape::Symbol(Box::from(name)),
        Vec::new(),
        measure,
    ))
}

/// The number node of `value`: checks the bits of `value` against
/// `max_integer_bits` of the receiving context, then checks and charges as
/// [`make`] does.
pub(super) fn number(value: Rational, context: &mut Context) -> Result<Term> {
    context.check(LimitField::IntegerBits, rational_bits(&value))?;
    make(TermShape::Number(value), Vec::new(), context)
}

/// The work of building a node with `children` children: one unit for the
/// node and one per child.
fn node_charge(children: usize) -> u64 {
    (children as u64).saturating_add(1)
}

/// The checks of a new node whose own bytes are `own` and whose children are
/// `children`: the depth against `max_depth`, then the tree size and the
/// logical bytes with `check_storage` at scope `Value`.
fn admit(
    own: Option<u64>,
    negative: bool,
    children: &[Term],
    context: &Context,
) -> Result<NodeMeasure> {
    let totals = child_totals(children);
    let depth = match totals.depth.checked_add(1) {
        Some(depth) => depth,
        None => return Err(beyond_every_limit(LimitField::Depth, context)),
    };
    context.check(LimitField::Depth, depth)?;
    let size = add_option(totals.size, 1);
    let bytes = match own {
        Some(own) => add_option(totals.bytes, own),
        None => None,
    };
    let cost = admitted_cost(size, bytes, context)?;
    Ok(NodeMeasure {
        size: cost.nodes,
        depth,
        bytes: cost.bytes,
        negative: negative || totals.negative,
    })
}

/// Checks the cost of a new term at scope `Value`, together with the open
/// frames and the reserved temporaries. A component that does not fit in a
/// `u64` exceeds every limit; the nodes are reported before the bytes.
fn admitted_cost(size: Option<u64>, bytes: Option<u64>, context: &Context) -> Result<Storage> {
    match size {
        None => Err(beyond_every_limit(LimitField::Nodes, context)),
        Some(nodes) => match bytes {
            None => {
                context.check_storage(Storage::new(nodes, 0), LimitScope::Value)?;
                Err(beyond_every_limit(LimitField::StorageBytes, context))
            }
            Some(bytes) => {
                let cost = Storage::new(nodes, bytes);
                context.check_storage(cost, LimitScope::Value)?;
                Ok(cost)
            }
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

/// The sums over `children`, one step per child.
fn child_totals(children: &[Term]) -> ChildTotals {
    let mut totals = ChildTotals {
        size: Some(0),
        bytes: Some(0),
        depth: 0,
        negative: false,
    };
    let mut index = 0;
    while index < children.len() {
        let child = &children[index].0;
        totals.size = add_option(totals.size, child.size);
        totals.bytes = add_option(totals.bytes, child.bytes);
        if child.depth > totals.depth {
            totals.depth = child.depth;
        }
        if child.negative {
            totals.negative = true;
        }
        index += 1;
    }
    totals
}

/// `total + value`, or `None` when `total` is `None` or the sum does not fit
/// in a `u64`.
fn add_option(total: Option<u64>, value: u64) -> Option<u64> {
    match total {
        Some(total) => total.checked_add(value),
        None => None,
    }
}

/// Allocates the node; the checks and the charge have passed.
fn allocate(shape: TermShape, children: Vec<Term>, measure: NodeMeasure) -> Term {
    Term(Rc::new(TermNode {
        shape,
        children,
        size: measure.size,
        depth: measure.depth,
        bytes: measure.bytes,
        negative: measure.negative,
    }))
}

/// Whether `term` is a sum.
pub(super) fn is_sum(term: &Term) -> bool {
    matches!(term.0.shape, TermShape::Sum(_, _))
}

/// Whether `shape` is a power with a negative exponent.
pub(super) fn is_negative_power(shape: &TermShape) -> bool {
    match shape {
        TermShape::Power(exponent) => *exponent < 0,
        TermShape::Number(_)
        | TermShape::Symbol(_)
        | TermShape::Call(_)
        | TermShape::Product(_)
        | TermShape::Sum(_, _) => false,
    }
}

/// The logical bytes that a node of `shape` with `children` children adds to
/// those of its children, by the canonical binary rendering of the contract:
/// a number counts as a rational, a symbol its bytes, and each binary sum,
/// product or power 4. `None` when the amount does not fit in a `u64`.
fn shape_bytes(shape: &TermShape, children: usize) -> Option<u64> {
    match shape {
        TermShape::Number(value) => Some(value.storage().bytes),
        TermShape::Symbol(name) => Some(name.len() as u64),
        TermShape::Call(head) => call_bytes(head, children),
        TermShape::Power(exponent) => Some(exponent::rendered_bytes(*exponent).saturating_add(4)),
        TermShape::Product(coefficient) => product_bytes(coefficient, children),
        TermShape::Sum(constant, coefficients) => sum_bytes(constant, coefficients),
    }
}

/// The bytes of a reserved call: its head name and 4 per argument.
fn call_bytes(head: &CallHead, arguments: usize) -> Option<u64> {
    match (arguments as u64).checked_mul(4) {
        Some(operators) => operators.checked_add(head.name.len() as u64),
        None => None,
    }
}

/// The bytes of a product with `factors` factors besides those of the
/// factors: its coefficient when it is not 1, written as one more factor,
/// and 4 per operator between the operands.
fn product_bytes(coefficient: &Rational, factors: usize) -> Option<u64> {
    let operands = factors as u64;
    if is_one(coefficient) {
        return operators(operands);
    }
    match operators(operands.saturating_add(1)) {
        Some(operators) => operators.checked_add(coefficient.storage().bytes),
        None => None,
    }
}

/// The bytes of a sum besides those of the cores of its monomials: its
/// constant when it is not 0, written as one more summand; the coefficient of
/// every monomial whose coefficient is not 1, written as a product with its
/// core; and 4 per operator between the summands.
fn sum_bytes(constant: &Rational, coefficients: &[Rational]) -> Option<u64> {
    let monomials = coefficients.len() as u64;
    let scaled = scaled_monomial_bytes(coefficients);
    if constant.is_zero() {
        return match (operators(monomials), scaled) {
            (Some(operators), Some(scaled)) => operators.checked_add(scaled),
            _ => None,
        };
    }
    match (operators(monomials.saturating_add(1)), scaled) {
        (Some(operators), Some(scaled)) => match operators.checked_add(scaled) {
            Some(total) => total.checked_add(constant.storage().bytes),
            None => None,
        },
        _ => None,
    }
}

/// The bytes that the coefficients of a sum add to its cores: the
/// coefficient and one operator for each coefficient that is not 1.
fn scaled_monomial_bytes(coefficients: &[Rational]) -> Option<u64> {
    let mut total: Option<u64> = Some(0);
    let mut index = 0;
    while index < coefficients.len() {
        if !is_one(&coefficients[index]) {
            let own = coefficients[index].storage().bytes.saturating_add(4);
            total = add_option(total, own);
        }
        index += 1;
    }
    total
}

/// The bytes of the operators between `operands` operands: 4 for each of
/// the `operands - 1` binary operations.
fn operators(operands: u64) -> Option<u64> {
    operands.saturating_sub(1).checked_mul(4)
}

/// `left + right` for the constants and coefficients of the term core: an
/// operand 0 gives the other operand, after checking its bits against
/// `max_integer_bits` and charging one unit, as an addition of rationals
/// does; otherwise the addition of rationals, with its bound. So the start
/// 0 of a sum adds no bits to the bound of its first number.
pub(super) fn add_rationals(
    left: &Rational,
    right: &Rational,
    context: &mut Context,
) -> Result<Rational> {
    if left.is_zero() {
        return pass_rational(right, context);
    }
    if right.is_zero() {
        return pass_rational(left, context);
    }
    left.add(right, context)
}

/// `left * right` for the coefficients of the term core: an operand 1 gives
/// the other operand, after checking its bits against `max_integer_bits`
/// and charging one unit, and an operand -1 the negation of the other;
/// otherwise the multiplication of rationals, with its bound. So the start 1
/// of a product, and the -1 of a negation, add no bits to the bound.
pub(super) fn multiply_rationals(
    left: &Rational,
    right: &Rational,
    context: &mut Context,
) -> Result<Rational> {
    if is_one(left) {
        return pass_rational(right, context);
    }
    if is_one(right) {
        return pass_rational(left, context);
    }
    if is_minus_one(left) {
        return right.negate(context);
    }
    if is_minus_one(right) {
        return left.negate(context);
    }
    left.multiply(right, context)
}

/// `value` itself, after checking its bits against `max_integer_bits` and
/// charging one unit.
fn pass_rational(value: &Rational, context: &mut Context) -> Result<Rational> {
    context.check(LimitField::IntegerBits, rational_bits(value))?;
    context.charge(1)?;
    Ok(value.clone())
}

/// Whether `value` is 1, without allocating.
pub(super) fn is_one(value: &Rational) -> bool {
    value.is_integer() && value.is_positive() && value.numerator().bits() == 1
}

/// Whether `value` is -1, without allocating.
pub(super) fn is_minus_one(value: &Rational) -> bool {
    value.is_integer() && value.is_negative() && value.numerator().bits() == 1
}

/// The bits of a rational, the quantity that `max_integer_bits` bounds: the
/// larger bit length of its parts.
pub(super) fn rational_bits(value: &Rational) -> u64 {
    let numerator = value.numerator().bits();
    let denominator = value.denominator().bits();
    if numerator > denominator {
        numerator
    } else {
        denominator
    }
}

/// The first child of `term`: the base of a power, or the only factor of a
/// product.
pub(super) fn first_child(term: &Term) -> Result<Term> {
    match term.0.children.first() {
        Some(child) => Ok(child.clone()),
        None => Err(internal("a node without its first child")),
    }
}

/// The fault of a broken internal invariant of the term core.
pub(super) fn internal(message: &str) -> Error {
    Error::new(FaultKind::Internal, None, message)
}
