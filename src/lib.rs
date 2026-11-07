//! kalyx, the computer algebra library of casξ.
//!
//! The library is being built from its foundations. So far it holds the
//! types of its errors and result states: [`Error`], with its [`ErrorKind`]
//! and the [`LimitExceeded`] record of a request limit, and [`Settled`], which
//! carries a value or a [`MathState`]; and the request [`Context`] with its
//! [`Limits`], which charges work, observes the deadline and cancellation,
//! bounds output and accounts for frames and temporaries. The rest of the
//! context is in the [`context`] module. The [`number`] module holds the
//! exact integers and rationals, the [`coefficient`] module the
//! coefficient-field trait with the field of rationals, and the [`term`]
//! module the term core: one immutable representation of numbers, symbols,
//! sums, products and integer powers, kept in canonical form.

#![forbid(unsafe_code)]
#![deny(clippy::float_arithmetic)]

// The library supports only 64-bit targets.
const _: () = assert!(usize::BITS == 64, "kalyx supports only 64-bit targets");

pub mod coefficient;
pub mod context;
mod error;
pub mod number;
pub mod term;

pub use context::{Context, Limits};
pub use error::{
    Error, ErrorClass, ErrorKind, FaultKind, LimitAmount, LimitExceeded, LimitField, LimitId,
    LimitScope, MathState, Result, Settled, Span,
};
