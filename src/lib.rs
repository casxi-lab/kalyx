//! kalyx, the computer algebra library of casξ.
//!
//! The library is being built from its foundations. So far it holds the
//! types of its errors and result states: [`Error`], with its [`ErrorKind`],
//! its [`CauseFrame`] records and the [`LimitExceeded`] record of a request
//! limit, and [`Settled`], which carries a value or a [`MathState`]; the
//! shared result types [`Evidence`], the evidence of a decision, and
//! [`Truth`], a three-valued truth value; and the request [`Context`] with
//! its [`Limits`], which charges work, observes the deadline and
//! cancellation, bounds output and accounts for frames and temporaries. The
//! rest of the context is in the [`context`] module. The [`number`] module
//! holds the
//! exact integers and rationals, the [`coefficient`] module the
//! coefficient-field trait with the field of rationals and the prime fields,
//! and the [`term`]
//! module the term core: one immutable representation of numbers, symbols,
//! sums, products and integer powers, kept in canonical form. The [`syntax`]
//! module holds the one grammar of the library's input, and [`parse`] reads
//! an expression in it into a term. The [`polynomial`] module holds the
//! univariate polynomials over a coefficient ring, with the expansion of
//! terms into polynomials over $\mathbb{Q}$, the conversion back to terms and
//! differentiation. The [`command`] module holds the command entry:
//! [`execute`] runs a [`Request`] under a context and returns its
//! [`Outcome`], and [`command::serialize`] writes an outcome as the line
//! bytes that are the only output format of the library.
//!
//! The public names of this crate root are listed in `api/root-names.txt`,
//! and a test fails when the two differ.

#![forbid(unsafe_code)]
#![deny(clippy::float_arithmetic)]

// The library supports only 64-bit targets.
const _: () = assert!(usize::BITS == 64, "kalyx supports only 64-bit targets");

pub mod coefficient;
pub mod command;
pub mod context;
mod error;
pub mod number;
pub mod polynomial;
mod registry;
mod shared;
pub mod syntax;
pub mod term;

pub use command::{Outcome, Request, execute};
pub use context::{Context, Limits};
pub use error::{
    CauseFrame, Error, ErrorClass, ErrorKind, FaultKind, LimitAmount, LimitExceeded, LimitField,
    LimitId, LimitScope, MathState, Result, Settled, Span,
};
pub use shared::{Evidence, Truth};
pub use syntax::parse;
