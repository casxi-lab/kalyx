//! kalyx, the computer algebra library of casξ.
//!
//! The library is being built from its foundations and has no public items
//! yet.

#![forbid(unsafe_code)]
#![deny(clippy::float_arithmetic)]

// The library supports only 64-bit targets.
const _: () = assert!(usize::BITS == 64, "kalyx supports only 64-bit targets");
