//! The input syntax: the one grammar of the library's input, read into terms
//! of the term core.
//!
//! [`parse`] reads an expression of numbers, identifiers, `+`, `-`, `*`,
//! `/`, `^`, parentheses and unary minus, and returns its canonical
//! [`Term`]. Reading and canonicalization are two separate stages: the
//! parser first reads the whole input into a private syntax tree, with an
//! explicit stack and without evaluating anything, so every syntax error is
//! reported before any term is built; the builder then turns the tree into a
//! term through the constructors of the term core. Neither stage recurses
//! natively, so the native stack use of `parse` does not grow with the
//! nesting of the input.
//!
//! The grammar, with its precedence and associativity, the lexical rules of
//! numbers and identifiers, the reserved names and the mapping to the term
//! core, is stated in `docs/semantics.md`; the limits, charges, spans and
//! errors of the parser are stated in the component contract,
//! `docs/components/syntax/contract.md`.
//!
//! ```
//! use kalyx::context::CancelFlag;
//! use kalyx::syntax::parse;
//! use kalyx::{Context, ErrorKind, FaultKind, Limits, Span};
//!
//! let mut context = Context::new(Limits::new(), CancelFlag::new());
//! let term = parse("-2^2 + 2^3^2", &mut context)?;
//! assert_eq!(term.display(&mut context)?, "508");
//! let term = parse("(y + x)^2 / 2", &mut context)?;
//! assert_eq!(term.display(&mut context)?, "1/2*(x + y)^2");
//!
//! let error = parse("2^(1/2)", &mut context).unwrap_err();
//! assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::NonIntegerExponent));
//! assert_eq!(error.span(), Span::new(2, 7));
//! let error = parse("sin(x)", &mut context).unwrap_err();
//! assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Unsupported));
//! assert_eq!(error.span(), Span::new(0, 4));
//! # Ok::<(), kalyx::Error>(())
//! ```

mod build;
mod lexer;
mod parser;
#[cfg(test)]
mod tests;
mod tree;

use crate::term::Term;
use crate::{Context, Result};

/// The canonical term of the expression `source`.
///
/// `source` is read in the grammar of `docs/semantics.md`: numbers such as
/// `12` and `1.5`, identifiers, `+`, `-`, `*`, `/`, `^`, parentheses and
/// unary minus, where `^` binds tightest and is right-associative, a unary
/// minus binds less tightly than `^`, and `*`, `/`, `+` and `-` are
/// left-associative in the usual order, so `-2^2 + 2^3^2` is 508. The term is
/// built through the constructors of the term core: a subtraction adds the
/// negation of its operand, a division multiplies by the power $-1$ of its
/// divisor, and the exponent of a power must be an integer constant.
///
/// Before it reads any byte, `parse` checks the length of `source` against
/// `max_input_bytes`. While it reads, it compares the nesting of the input
/// with `max_depth` and checks the count of syntax nodes with
/// `check_storage` at scope `Value`. Every step is charged, and every error
/// carries the byte span of the text that caused it: an empty span at the end
/// for incomplete input, and for an error of the term core the span of the
/// syntax node whose term failed.
///
/// # Errors
///
/// - `Fault(Syntax)` for input outside the grammar, such as `2x`, `.5`,
///   `1e-3`, `1 +` or `(1`;
/// - `Fault(Unsupported)` for function-call syntax, an identifier followed
///   by `(`, and for the names reserved for constants, `pi`, `i` and
///   `undefined`;
/// - `Fault(NonIntegerExponent)` for an exponent that is not an integer
///   constant, and `Fault(DivisionByZero)` for a division by zero or a
///   negative power of zero, which are evaluated strictly;
/// - `ResourceLimit` with `LimitField::InputBytes`, `LimitField::Depth` or
///   `LimitField::Nodes` for the limits of the parser, and the limits of the
///   decimal literals and of the term core;
/// - the request failures of the charges, and `Fault(Internal)` when an
///   internal invariant is broken.
pub fn parse(source: &str, context: &mut Context) -> Result<Term> {
    let tree = parser::read(source, context)?;
    build::build(source, tree, context)
}
