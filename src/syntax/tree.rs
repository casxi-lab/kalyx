//! The syntax tree: the parsed form of an input, before any term is built.
//!
//! The tree is a vector of nodes in postorder: every node comes after the
//! nodes of its operands, which it names by their indices, so the root is the
//! last node and the builder takes the nodes in order. A chain of `+` and `-`,
//! or of `*` and `/`, is one node with its operands in order; the operand
//! after a `-` is its negation and the operand after a `/` its reciprocal,
//! each a node of its own right after the nodes of the operand, so the
//! builder applies them, as a left-associative reading does, before it builds
//! the next operand. Parentheses add no node; they widen the range of the
//! operand that they enclose.

use crate::number::Rational;
use crate::{Error, FaultKind, Result, Span};

/// A byte range of the source, from `start` up to, but not including, `end`.
/// Every range of the parser has `start <= end`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct SyntaxRange {
    pub(super) start: usize,
    pub(super) end: usize,
}

impl SyntaxRange {
    /// The range from `start` up to `end`.
    pub(super) const fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    /// The span of the range, for an error.
    pub(super) const fn span(self) -> Option<Span> {
        Span::new(self.start, self.end)
    }

    /// The range from the start of `self` to the end of `last`.
    pub(super) const fn through(self, last: Self) -> Self {
        Self::new(self.start, last.end)
    }
}

/// The operator in front of an operand of a chain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SyntaxOperator {
    /// The first operand of a chain, with no operator in front of it.
    Leading,
    /// `+`.
    Add,
    /// `-` between two operands.
    Subtract,
    /// `*`.
    Multiply,
    /// `/`.
    Divide,
}

/// An operand of a chain.
#[derive(Clone, Copy, Debug)]
pub(super) struct SyntaxOperand {
    /// The operator in front of the operand.
    pub(super) operator: SyntaxOperator,
    /// The index of the node of the operand: after a `-` the node of its
    /// negation, and after a `/` the node of its reciprocal.
    pub(super) node: usize,
    /// The range of the operation that the operand completes: from the start
    /// of the chain to the end of the operand, with its parentheses; for the
    /// leading operand, the range of the operand with its parentheses.
    pub(super) range: SyntaxRange,
}

/// The shape of a syntax node.
#[derive(Debug)]
pub(super) enum SyntaxShape {
    /// A number literal, with its exact value.
    Number(Rational),
    /// An identifier, whose name is the text of the range of the node.
    Symbol,
    /// A unary minus, or the operand after a `-` of a chain, negated: the
    /// index of the operand.
    Negate(usize),
    /// The operand after a `/` of a chain, raised to the power $-1$: the index
    /// of the operand.
    Reciprocal(usize),
    /// A power, with the indices of its base and its exponent and the range
    /// of the exponent with its parentheses.
    Power {
        base: usize,
        exponent: usize,
        exponent_range: SyntaxRange,
    },
    /// A chain of `+` and `-`, with its operands in order.
    Sum(Vec<SyntaxOperand>),
    /// A chain of `*` and `/`, with its operands in order.
    Product(Vec<SyntaxOperand>),
}

/// A node of the syntax tree.
#[derive(Debug)]
pub(super) struct SyntaxNode {
    /// The shape of the node.
    pub(super) shape: SyntaxShape,
    /// The range of the node, without the parentheses around it: the token of
    /// a number or an identifier, from a unary minus to the end of its
    /// operand, from the start of the base of a power to the end of its
    /// exponent, from the start of the first operand of a chain to the end of
    /// its last, and for the negation or the reciprocal of an operand of a
    /// chain, the operation that it completes, from the start of the chain to
    /// the end of the operand.
    pub(super) range: SyntaxRange,
}

/// The syntax tree of an input: its nodes in postorder, the root last.
#[derive(Debug)]
pub(super) struct SyntaxTree {
    pub(super) nodes: Vec<SyntaxNode>,
}

/// The text of `range` in `source`.
///
/// # Errors
///
/// `Fault(Internal)` when the range is not a range of whole characters of
/// the source, which no token of the lexer is.
pub(super) fn text_at(source: &str, range: SyntaxRange) -> Result<&str> {
    match source.get(range.start..range.end) {
        Some(text) => Ok(text),
        None => Err(Error::new(
            FaultKind::Internal,
            range.span(),
            "a syntax range outside the source",
        )),
    }
}
