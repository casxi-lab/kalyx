//! Unit tests of the stages of the parser: the tokens and their charges, the
//! shape of the syntax tree, and the operation spans that the builder puts on
//! the errors of the term core.

use super::lexer::{SyntaxTokenKind, next_token};
use super::parser::read;
use super::tree::{SyntaxOperator, SyntaxRange, SyntaxShape, SyntaxTree};
use crate::context::CancelFlag;
use crate::{Context, Limits};

fn context() -> Context {
    Context::new(Limits::new(), CancelFlag::new())
}

/// The kinds and ranges of the tokens of `source`, up to the end, and the
/// work that reading them charged.
fn tokens(source: &str) -> (Vec<(SyntaxTokenKind, usize, usize)>, u64) {
    let mut context = context();
    let mut position = 0;
    let mut read = Vec::new();
    loop {
        let token = next_token(source, &mut position, &mut context).unwrap();
        read.push((token.kind, token.range.start, token.range.end));
        if matches!(token.kind, SyntaxTokenKind::End) {
            return (read, context.work_used());
        }
    }
}

fn tree(source: &str) -> SyntaxTree {
    read(source, &mut context()).unwrap()
}

// A literal runs over letters, digits, `_` and points; an identifier over
// letters, digits and `_`; whitespace separates tokens; reading the whole
// input charges its bytes and one unit for its end.
#[test]
fn tokens_cover_the_input_and_charge_its_bytes() {
    use SyntaxTokenKind::{Caret, Close, End, Identifier, Minus, Number, Open, Plus, Slash, Star};
    let source = " x_1+(2.5e3)*-y^\t2/ 1.x ";
    let (read, work) = tokens(source);
    assert_eq!(
        read,
        vec![
            (Identifier, 1, 4),
            (Plus, 4, 5),
            (Open, 5, 6),
            (Number, 6, 11),
            (Close, 11, 12),
            (Star, 12, 13),
            (Minus, 13, 14),
            (Identifier, 14, 15),
            (Caret, 15, 16),
            (Number, 17, 18),
            (Slash, 18, 19),
            (Number, 20, 23),
            (End, 24, 24),
        ]
    );
    assert_eq!(work, source.len() as u64 + 1);
    assert_eq!(tokens(""), (vec![(End, 0, 0)], 1));
}

// The nodes are in postorder: every operand comes before the node that holds
// it, each node is held once, and the root is the last node.
#[test]
fn the_tree_is_in_postorder_with_the_root_last() {
    for source in [
        "-2^2 + 2^3^2",
        "((x))",
        "a*b/c - -d^-e",
        "(1 + 2) * x / (3 - y)^2",
    ] {
        let nodes = tree(source).nodes;
        let mut held = vec![0_u32; nodes.len()];
        for (index, node) in nodes.iter().enumerate() {
            let operands: Vec<usize> = match &node.shape {
                SyntaxShape::Number(_) | SyntaxShape::Symbol => Vec::new(),
                SyntaxShape::Negate(operand) | SyntaxShape::Reciprocal(operand) => {
                    vec![*operand]
                }
                SyntaxShape::Power { base, exponent, .. } => vec![*base, *exponent],
                SyntaxShape::Sum(operands) | SyntaxShape::Product(operands) => {
                    operands.iter().map(|operand| operand.node).collect()
                }
            };
            for operand in operands {
                assert!(operand < index, "{source}");
                held[operand] += 1;
            }
        }
        let root = nodes.len() - 1;
        for (index, count) in held.iter().enumerate() {
            assert_eq!(*count, u32::from(index != root), "{source}");
        }
    }
}

// A chain is one node; each operand after the first carries the range of
// the operation it completes, from the start of the chain, and parentheses
// widen the range of an operand but not the range of its node. The operand
// after a `/` or a `-` is its reciprocal or its negation, a node over the
// range of the operation right after the nodes of the operand, before the
// nodes of the next operand.
#[test]
fn chains_keep_the_ranges_of_their_operations() {
    let nodes = tree("(a)*b/c*d").nodes;
    let SyntaxShape::Product(operands) = &nodes[5].shape else {
        panic!("a product chain: {:?}", nodes[5]);
    };
    let operations: Vec<(SyntaxOperator, usize, SyntaxRange)> = operands
        .iter()
        .map(|operand| (operand.operator, operand.node, operand.range))
        .collect();
    assert_eq!(
        operations,
        vec![
            (SyntaxOperator::Leading, 0, SyntaxRange::new(0, 3)),
            (SyntaxOperator::Multiply, 1, SyntaxRange::new(0, 5)),
            (SyntaxOperator::Divide, 3, SyntaxRange::new(0, 7)),
            (SyntaxOperator::Multiply, 4, SyntaxRange::new(0, 9)),
        ]
    );
    assert!(matches!(nodes[3].shape, SyntaxShape::Reciprocal(2)));
    assert_eq!(nodes[3].range, SyntaxRange::new(0, 7));
    assert_eq!(nodes[0].range, SyntaxRange::new(1, 2));
    assert_eq!(nodes[5].range, SyntaxRange::new(0, 9));
    let nodes = tree("1 - (2 + 3)").nodes;
    let SyntaxShape::Sum(operands) = &nodes[5].shape else {
        panic!("a sum chain: {:?}", nodes[5]);
    };
    assert_eq!(operands[1].operator, SyntaxOperator::Subtract);
    assert_eq!(operands[1].node, 4);
    assert_eq!(operands[1].range, SyntaxRange::new(0, 11));
    assert!(matches!(nodes[4].shape, SyntaxShape::Negate(3)));
    assert_eq!(nodes[4].range, SyntaxRange::new(0, 11));
    assert_eq!(nodes[3].range, SyntaxRange::new(5, 10));
}

// The exponent of a power keeps its range with its parentheses, for the
// errors of the exponent; a unary minus runs from its sign to the end of its
// operand.
#[test]
fn powers_and_negations_keep_their_ranges() {
    let nodes = tree("x^(-1)").nodes;
    assert_eq!(nodes[2].range, SyntaxRange::new(3, 5));
    let SyntaxShape::Power { exponent_range, .. } = &nodes[3].shape else {
        panic!("a power: {:?}", nodes[3]);
    };
    assert_eq!(*exponent_range, SyntaxRange::new(2, 6));
    assert_eq!(nodes[3].range, SyntaxRange::new(0, 6));
}
