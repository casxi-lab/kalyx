//! kalyx, the computer algebra library of casξ.
//!
//! The library is being built from its foundations. So far it holds the
//! types of its errors and result states: [`Error`], with its [`ErrorKind`]
//! and the [`LimitExceeded`] record of a request limit, and [`Settled`], which
//! carries a value or a [`MathState`]. No entry of the library computes yet.

#![forbid(unsafe_code)]
#![deny(clippy::float_arithmetic)]

// The library supports only 64-bit targets.
const _: () = assert!(usize::BITS == 64, "kalyx supports only 64-bit targets");

mod error;

pub use error::{
    Error, ErrorClass, ErrorKind, FaultKind, LimitAmount, LimitExceeded, LimitField, LimitId,
    LimitScope, MathState, Result, Settled, Span,
};
