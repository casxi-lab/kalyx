//! The parser: reads the tokens of an input into its syntax tree, in one loop
//! over an explicit stack of open constructs.
//!
//! The parser reads an operand, then the token after it. A unary minus, an
//! opening parenthesis and the `^` of a power open a construct whose operand
//! is read next; a binary operator either continues the chain on top of the
//! stack, when it has the precedence of that chain, or first closes, one per
//! step, the constructs that bind more tightly than it. A `)` closes the
//! constructs down to its `(`, and the end of the input closes all of them.
//! The precedence, from the tightest: `^`, which is right-associative, then a
//! unary minus, then `*` and `/`, then `+` and `-`, both left-associative.
//!
//! Every operand is read at a level: the whole input at level 1, and one
//! level deeper the contents of parentheses, the operand of a unary minus,
//! the exponent of a power and every operand of a chain after its first. The
//! level of an operand is compared with `max_depth` before the parser reads
//! it. Each syntax node, a number, an identifier, a unary minus, a power and
//! each operator of a chain, is checked with `check_storage` at scope `Value`
//! as the count of syntax nodes so far, with no bytes, and charged one unit
//! when it is complete.

use crate::context::Storage;
use crate::number::Rational;
use crate::term::is_reserved;
use crate::{Context, Error, FaultKind, LimitField, LimitScope, Result};

use super::lexer::{SyntaxToken, SyntaxTokenKind, next_token};
use super::tree::{
    SyntaxNode, SyntaxOperand, SyntaxOperator, SyntaxRange, SyntaxShape, SyntaxTree, text_at,
};

/// The work units charged for each syntax node, after its check.
const NODE_CHARGE: u64 = 1;

/// A complete operand: its node, its range with the parentheses around it,
/// and the level at which it was read.
#[derive(Clone, Copy, Debug)]
struct SyntaxPart {
    node: usize,
    outer: SyntaxRange,
    level: u64,
}

/// The two kinds of chains.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SyntaxChainKind {
    /// A chain of `+` and `-`.
    Sum,
    /// A chain of `*` and `/`.
    Product,
}

/// An open chain whose next operand is being read: its operands so far, the
/// operator in front of the next one, the start of its first operand and its
/// level, the level of its first operand.
#[derive(Debug)]
struct SyntaxChain {
    kind: SyntaxChainKind,
    operands: Vec<SyntaxOperand>,
    pending: SyntaxOperator,
    start: usize,
    level: u64,
}

/// An open construct on the stack of the parser.
#[derive(Debug)]
enum SyntaxFrame {
    /// An opening parenthesis at byte `open`; the parenthesized operand is
    /// at `level`, and its contents one level deeper.
    Group { open: usize, level: u64 },
    /// A unary minus at byte `start`, at `level`; its operand is one level
    /// deeper.
    Negate { start: usize, level: u64 },
    /// A power with its base; the exponent is one level deeper than the base.
    Power { base: SyntaxPart },
    /// A chain of `+` and `-`, or of `*` and `/`.
    Chain(SyntaxChain),
}

/// The next step of the parser.
#[derive(Debug)]
enum SyntaxStep {
    /// Read an operand at this level.
    Operand(u64),
    /// Read the token after this operand.
    Operator(SyntaxPart),
    /// Apply this token, already read, after this operand.
    Follow(SyntaxPart, SyntaxToken),
}

/// The state of the parser: the position of the lexer, the nodes so far, the
/// stack of open constructs and the count of syntax nodes.
struct SyntaxParser {
    position: usize,
    nodes: Vec<SyntaxNode>,
    frames: Vec<SyntaxFrame>,
    count: u64,
}

/// Reads `source` into its syntax tree.
///
/// Checks the bytes of the source against `max_input_bytes` and the level 1
/// of the whole input against `max_depth`, both with the span of the whole
/// source, before it reads any byte; then reads the tokens.
///
/// # Errors
///
/// `ResourceLimit` with `LimitField::InputBytes`, `LimitField::Depth` or
/// `LimitField::Nodes`; `Fault(Syntax)`; `Fault(Unsupported)` for
/// function-call syntax and the reserved names; the errors of the decimal
/// literal function; and the request failures of the charges.
pub(super) fn read(source: &str, context: &mut Context) -> Result<SyntaxTree> {
    let whole = SyntaxRange::new(0, source.len());
    context.check_at(LimitField::InputBytes, source.len() as u64, whole.span())?;
    context.check_at(LimitField::Depth, 1, whole.span())?;
    read_tokens(source, context)
}

/// Reads the tokens of `source` until the input is complete.
fn read_tokens(source: &str, context: &mut Context) -> Result<SyntaxTree> {
    let mut parser = SyntaxParser {
        position: 0,
        nodes: Vec::new(),
        frames: Vec::new(),
        count: 0,
    };
    let mut step = SyntaxStep::Operand(1);
    while let Some(next) = advance(source, &mut parser, step, context)? {
        step = next;
    }
    Ok(SyntaxTree {
        nodes: parser.nodes,
    })
}

/// Takes one step, and returns the next one, or `None` when the input is
/// complete and its root is the last node.
fn advance(
    source: &str,
    parser: &mut SyntaxParser,
    step: SyntaxStep,
    context: &mut Context,
) -> Result<Option<SyntaxStep>> {
    match step {
        SyntaxStep::Operand(level) => {
            let token = next_token(source, &mut parser.position, context)?;
            let next = operand(source, parser, token, level, context)?;
            Ok(Some(next))
        }
        SyntaxStep::Operator(part) => {
            let token = next_token(source, &mut parser.position, context)?;
            follow(parser, part, token, context)
        }
        SyntaxStep::Follow(part, token) => follow(parser, part, token, context),
    }
}

/// Starts the operand that `token` begins, at `level`.
fn operand(
    source: &str,
    parser: &mut SyntaxParser,
    token: SyntaxToken,
    level: u64,
    context: &mut Context,
) -> Result<SyntaxStep> {
    match token.kind {
        SyntaxTokenKind::Minus => {
            let inner = deeper(level, token.range, context)?;
            parser.frames.push(SyntaxFrame::Negate {
                start: token.range.start,
                level,
            });
            Ok(SyntaxStep::Operand(inner))
        }
        SyntaxTokenKind::Open => {
            let inner = deeper(level, token.range, context)?;
            parser.frames.push(SyntaxFrame::Group {
                open: token.range.start,
                level,
            });
            Ok(SyntaxStep::Operand(inner))
        }
        SyntaxTokenKind::Number => {
            let text = text_at(source, token.range)?;
            let value = Rational::literal_at(text, token.range.start, context)?;
            let part = parser.node(SyntaxShape::Number(value), token.range, level, context)?;
            Ok(SyntaxStep::Operator(part))
        }
        SyntaxTokenKind::Identifier => identifier(source, parser, token, level, context),
        SyntaxTokenKind::Plus
        | SyntaxTokenKind::Star
        | SyntaxTokenKind::Slash
        | SyntaxTokenKind::Caret
        | SyntaxTokenKind::Close
        | SyntaxTokenKind::End => Err(syntax(
            token.range,
            "expected a number, an identifier, `-` or `(`",
        )),
    }
}

/// Reads the identifier `token` at `level`, which is a symbol unless it is a
/// reserved name or the name of function-call syntax; reads the token after
/// it to tell.
fn identifier(
    source: &str,
    parser: &mut SyntaxParser,
    token: SyntaxToken,
    level: u64,
    context: &mut Context,
) -> Result<SyntaxStep> {
    let name = text_at(source, token.range)?;
    if is_reserved(name.as_bytes()) {
        return Err(Error::new(
            FaultKind::Unsupported,
            token.range.span(),
            "the name is reserved for a constant of a later release",
        ));
    }
    let next = next_token(source, &mut parser.position, context)?;
    if matches!(next.kind, SyntaxTokenKind::Open) {
        return Err(Error::new(
            FaultKind::Unsupported,
            token.range.through(next.range).span(),
            "function calls are not supported in this release",
        ));
    }
    let part = parser.node(SyntaxShape::Symbol, token.range, level, context)?;
    Ok(SyntaxStep::Follow(part, next))
}

/// Applies `token`, the token after the complete operand `part`.
fn follow(
    parser: &mut SyntaxParser,
    part: SyntaxPart,
    token: SyntaxToken,
    context: &mut Context,
) -> Result<Option<SyntaxStep>> {
    match token.kind {
        SyntaxTokenKind::Caret => {
            let inner = deeper(part.level, token.range, context)?;
            parser.frames.push(SyntaxFrame::Power { base: part });
            Ok(Some(SyntaxStep::Operand(inner)))
        }
        SyntaxTokenKind::Number | SyntaxTokenKind::Identifier | SyntaxTokenKind::Open => Err(
            syntax(token.range, "expected an operator or the end of the input"),
        ),
        SyntaxTokenKind::Plus
        | SyntaxTokenKind::Minus
        | SyntaxTokenKind::Star
        | SyntaxTokenKind::Slash
        | SyntaxTokenKind::Close
        | SyntaxTokenKind::End => close(parser, part, token, context),
    }
}

/// Applies the binary operator, the `)` or the end of the input `token`
/// after the operand `part` to the construct on top of the stack: closes it
/// when it binds more tightly than the token, and otherwise continues it or
/// opens a new chain.
fn close(
    parser: &mut SyntaxParser,
    part: SyntaxPart,
    token: SyntaxToken,
    context: &mut Context,
) -> Result<Option<SyntaxStep>> {
    match parser.frames.pop() {
        None => outermost(parser, part, token, context),
        Some(SyntaxFrame::Group { open, level }) => {
            group(parser, part, token, open, level, context)
        }
        Some(SyntaxFrame::Negate { start, level }) => {
            let range = SyntaxRange::new(start, part.outer.end);
            let negation = parser.node(SyntaxShape::Negate(part.node), range, level, context)?;
            Ok(Some(SyntaxStep::Follow(negation, token)))
        }
        Some(SyntaxFrame::Power { base }) => {
            let shape = SyntaxShape::Power {
                base: base.node,
                exponent: part.node,
                exponent_range: part.outer,
            };
            let range = base.outer.through(part.outer);
            let power = parser.node(shape, range, base.level, context)?;
            Ok(Some(SyntaxStep::Follow(power, token)))
        }
        Some(SyntaxFrame::Chain(chain)) => chain_step(parser, chain, part, token, context),
    }
}

/// Applies `token` after the operand `part` when no construct is open.
fn outermost(
    parser: &mut SyntaxParser,
    part: SyntaxPart,
    token: SyntaxToken,
    context: &mut Context,
) -> Result<Option<SyntaxStep>> {
    match token.kind {
        SyntaxTokenKind::End => Ok(None),
        SyntaxTokenKind::Close => Err(syntax(token.range, "a `)` without a matching `(`")),
        SyntaxTokenKind::Plus
        | SyntaxTokenKind::Minus
        | SyntaxTokenKind::Star
        | SyntaxTokenKind::Slash => start_chain(parser, part, token, context),
        SyntaxTokenKind::Number
        | SyntaxTokenKind::Identifier
        | SyntaxTokenKind::Caret
        | SyntaxTokenKind::Open => Err(internal(token.range)),
    }
}

/// Applies `token` after the operand `part` inside the parentheses opened at
/// byte `open`, whose parenthesized operand is at `level`.
fn group(
    parser: &mut SyntaxParser,
    part: SyntaxPart,
    token: SyntaxToken,
    open: usize,
    level: u64,
    context: &mut Context,
) -> Result<Option<SyntaxStep>> {
    match token.kind {
        SyntaxTokenKind::Close => {
            let enclosed = SyntaxPart {
                node: part.node,
                outer: SyntaxRange::new(open, token.range.end),
                level,
            };
            Ok(Some(SyntaxStep::Operator(enclosed)))
        }
        SyntaxTokenKind::End => Err(syntax(token.range, "expected `)`")),
        SyntaxTokenKind::Plus
        | SyntaxTokenKind::Minus
        | SyntaxTokenKind::Star
        | SyntaxTokenKind::Slash => {
            parser.frames.push(SyntaxFrame::Group { open, level });
            start_chain(parser, part, token, context)
        }
        SyntaxTokenKind::Number
        | SyntaxTokenKind::Identifier
        | SyntaxTokenKind::Caret
        | SyntaxTokenKind::Open => Err(internal(token.range)),
    }
}

/// Applies `token` after the operand `part`, the operand that `chain` is
/// reading: continues the chain with an operator of its precedence, opens a
/// chain of products on it for `*` and `/` after a sum, and otherwise
/// completes the chain.
fn chain_step(
    parser: &mut SyntaxParser,
    chain: SyntaxChain,
    part: SyntaxPart,
    token: SyntaxToken,
    context: &mut Context,
) -> Result<Option<SyntaxStep>> {
    let continues = match (chain.kind, token.kind) {
        (SyntaxChainKind::Sum, SyntaxTokenKind::Plus | SyntaxTokenKind::Minus)
        | (SyntaxChainKind::Product, SyntaxTokenKind::Star | SyntaxTokenKind::Slash) => true,
        (SyntaxChainKind::Sum, SyntaxTokenKind::Star | SyntaxTokenKind::Slash) => {
            parser.frames.push(SyntaxFrame::Chain(chain));
            return start_chain(parser, part, token, context);
        }
        (
            SyntaxChainKind::Sum | SyntaxChainKind::Product,
            SyntaxTokenKind::Plus
            | SyntaxTokenKind::Minus
            | SyntaxTokenKind::Close
            | SyntaxTokenKind::End,
        ) => false,
        (
            SyntaxChainKind::Sum | SyntaxChainKind::Product,
            SyntaxTokenKind::Number
            | SyntaxTokenKind::Identifier
            | SyntaxTokenKind::Caret
            | SyntaxTokenKind::Open,
        ) => return Err(internal(token.range)),
    };
    if continues {
        continue_chain(parser, chain, part, token, context)
    } else {
        let whole = parser.finish(chain, part, context)?;
        Ok(Some(SyntaxStep::Follow(whole, token)))
    }
}

/// Opens a chain with the first operand `part` and the operator `token`.
fn start_chain(
    parser: &mut SyntaxParser,
    part: SyntaxPart,
    token: SyntaxToken,
    context: &mut Context,
) -> Result<Option<SyntaxStep>> {
    let (kind, pending) = match chain_operator(token) {
        Some(operator) => operator,
        None => return Err(internal(token.range)),
    };
    let inner = deeper(part.level, token.range, context)?;
    let leading = SyntaxOperand {
        operator: SyntaxOperator::Leading,
        node: part.node,
        range: part.outer,
    };
    parser.frames.push(SyntaxFrame::Chain(SyntaxChain {
        kind,
        operands: vec![leading],
        pending,
        start: part.outer.start,
        level: part.level,
    }));
    Ok(Some(SyntaxStep::Operand(inner)))
}

/// Adds the operand `part` to `chain` and continues it with the operator
/// `token`, of the precedence of the chain.
fn continue_chain(
    parser: &mut SyntaxParser,
    mut chain: SyntaxChain,
    part: SyntaxPart,
    token: SyntaxToken,
    context: &mut Context,
) -> Result<Option<SyntaxStep>> {
    let pending = match chain_operator(token) {
        Some((_, operator)) => operator,
        None => return Err(internal(token.range)),
    };
    let inner = deeper(chain.level, token.range, context)?;
    parser.append(&mut chain, part, context)?;
    chain.pending = pending;
    parser.frames.push(SyntaxFrame::Chain(chain));
    Ok(Some(SyntaxStep::Operand(inner)))
}

/// The chain and the operator of a binary operator token other than `^`.
const fn chain_operator(token: SyntaxToken) -> Option<(SyntaxChainKind, SyntaxOperator)> {
    match token.kind {
        SyntaxTokenKind::Plus => Some((SyntaxChainKind::Sum, SyntaxOperator::Add)),
        SyntaxTokenKind::Minus => Some((SyntaxChainKind::Sum, SyntaxOperator::Subtract)),
        SyntaxTokenKind::Star => Some((SyntaxChainKind::Product, SyntaxOperator::Multiply)),
        SyntaxTokenKind::Slash => Some((SyntaxChainKind::Product, SyntaxOperator::Divide)),
        SyntaxTokenKind::Number
        | SyntaxTokenKind::Identifier
        | SyntaxTokenKind::Caret
        | SyntaxTokenKind::Open
        | SyntaxTokenKind::Close
        | SyntaxTokenKind::End => None,
    }
}

impl SyntaxParser {
    /// Checks and charges one more syntax node, whose range is `range`.
    ///
    /// The count of syntax nodes, this one included, is checked with
    /// `check_storage` at scope `Value` as a cost of that many nodes and no
    /// bytes; then one unit is charged; only then is the count raised.
    fn complete(&mut self, range: SyntaxRange, context: &mut Context) -> Result<()> {
        let count = self.count.saturating_add(1);
        context.check_storage_at(Storage::new(count, 0), LimitScope::Value, range.span())?;
        context.charge_at(NODE_CHARGE, range.span())?;
        self.count = count;
        Ok(())
    }

    /// Completes the syntax node of `shape` over `range`, read at `level`,
    /// and adds it to the tree.
    fn node(
        &mut self,
        shape: SyntaxShape,
        range: SyntaxRange,
        level: u64,
        context: &mut Context,
    ) -> Result<SyntaxPart> {
        self.complete(range, context)?;
        let node = self.nodes.len();
        self.nodes.push(SyntaxNode { shape, range });
        Ok(SyntaxPart {
            node,
            outer: range,
            level,
        })
    }

    /// Completes the operation of the pending operator of `chain` with the
    /// operand `part`, a syntax node from the start of the chain to the end
    /// of `part`. After a `-` the operand is its negation, and after a `/` its
    /// reciprocal, each a node over that range right after the nodes of
    /// `part`.
    fn append(
        &mut self,
        chain: &mut SyntaxChain,
        part: SyntaxPart,
        context: &mut Context,
    ) -> Result<()> {
        let range = SyntaxRange::new(chain.start, part.outer.end);
        self.complete(range, context)?;
        let node = match chain.pending {
            SyntaxOperator::Subtract => self.operation(SyntaxShape::Negate(part.node), range),
            SyntaxOperator::Divide => self.operation(SyntaxShape::Reciprocal(part.node), range),
            SyntaxOperator::Leading | SyntaxOperator::Add | SyntaxOperator::Multiply => part.node,
        };
        chain.operands.push(SyntaxOperand {
            operator: chain.pending,
            node,
            range,
        });
        Ok(())
    }

    /// Adds the node of `shape` over `range`, the operation of an operand of
    /// a chain that `append` checked and charged, and returns its index.
    fn operation(&mut self, shape: SyntaxShape, range: SyntaxRange) -> usize {
        let node = self.nodes.len();
        self.nodes.push(SyntaxNode { shape, range });
        node
    }

    /// Completes `chain` with its last operand `part` and adds it to the tree
    /// as one node.
    fn finish(
        &mut self,
        mut chain: SyntaxChain,
        part: SyntaxPart,
        context: &mut Context,
    ) -> Result<SyntaxPart> {
        self.append(&mut chain, part, context)?;
        let range = SyntaxRange::new(chain.start, part.outer.end);
        let shape = match chain.kind {
            SyntaxChainKind::Sum => SyntaxShape::Sum(chain.operands),
            SyntaxChainKind::Product => SyntaxShape::Product(chain.operands),
        };
        let node = self.nodes.len();
        self.nodes.push(SyntaxNode { shape, range });
        Ok(SyntaxPart {
            node,
            outer: range,
            level: chain.level,
        })
    }
}

/// The level one deeper than `level`, after checking it against
/// `max_depth`, with the span of `range`, the token that opens it; charges
/// nothing.
fn deeper(level: u64, range: SyntaxRange, context: &Context) -> Result<u64> {
    let inner = level.saturating_add(1);
    context.check_at(LimitField::Depth, inner, range.span())?;
    Ok(inner)
}

/// A syntax error at `range`.
fn syntax(range: SyntaxRange, message: &str) -> Error {
    Error::new(FaultKind::Syntax, range.span(), message)
}

/// The fault of a state that the rules of the parser exclude, at `range`.
fn internal(range: SyntaxRange) -> Error {
    Error::new(
        FaultKind::Internal,
        range.span(),
        "the parser reached a state that its rules exclude",
    )
}
