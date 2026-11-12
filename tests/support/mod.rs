//! Generated inputs for the integration tests: a sequence from a fixed seed
//! and the report of a generated case that fails.
//!
//! The sequence is SplitMix64, written here; the tests use no external
//! generator. A seed therefore gives the same values in every test that
//! draws from it. When a test panics while a sequence is alive, the sequence
//! reports its seed and how many values it drew, which identify the
//! generated case that failed, and [`case`] reports the label of the case.
//! The methods below [`Sequence::next`] draw only through it.

use std::fmt;

use kalyx::context::CancelFlag;
use kalyx::number::{Integer, Rational};
use kalyx::{Context, Limits};

/// A fixed-seed SplitMix64 sequence for reproducible generated inputs.
pub struct Sequence {
    seed: u64,
    state: u64,
    drawn: u64,
}

impl Sequence {
    /// The sequence of `seed`.
    pub const fn new(seed: u64) -> Self {
        Self {
            seed,
            state: seed,
            drawn: 0,
        }
    }

    /// The next value of SplitMix64.
    pub fn next(&mut self) -> u64 {
        self.drawn += 1;
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A value in `low..=high`: `low` plus the next value modulo the size of
    /// the range, uniform up to the bias of the remainder.
    pub fn next_in(&mut self, low: i64, high: i64) -> i64 {
        let span = u64::try_from(high - low).unwrap() + 1;
        low + i64::try_from(self.next() % span).unwrap()
    }

    /// An index below `len`, which must be positive.
    pub fn index(&mut self, len: usize) -> usize {
        let high = i64::try_from(len).unwrap() - 1;
        usize::try_from(self.next_in(0, high)).unwrap()
    }

    /// One of `items`, which must not be empty.
    pub fn pick<'a, T>(&mut self, items: &'a [T]) -> &'a T {
        &items[self.index(items.len())]
    }

    /// A nonnegative integer below $2^{\mathit{bits}}$, assembled from
    /// draws of at most 31 bits each, most significant first; when `exact`
    /// holds and the top bit is clear, $2^{\mathit{bits} - 1}$ is added, so
    /// the integer has exactly `bits` bits. It is assembled with the
    /// arithmetic of `Rational` and serves only as an input, never as the
    /// expected value of a check.
    pub fn integer_bits(&mut self, bits: u64, exact: bool) -> Integer {
        let context = &mut Context::new(
            Limits::new()
                .with_max_work(u64::MAX)
                .with_max_integer_bits(bits + 64),
            CancelFlag::new(),
        );
        let mut value = Rational::from(0_i64);
        let mut filled = 0;
        while filled < bits {
            let width = (bits - filled).min(31);
            let draw = self.next_in(0, (1_i64 << width) - 1);
            let shift = Rational::from(1_i64 << width);
            value = value.multiply(&shift, context).unwrap();
            value = value.add(&Rational::from(draw), context).unwrap();
            filled += width;
        }
        if exact && bits > 0 && value.numerator().bits() < bits {
            let exponent = i64::try_from(bits - 1).unwrap();
            let top = Rational::from(2_i64).power(exponent, context).unwrap();
            value = value.add(&top, context).unwrap();
        }
        value.numerator().clone()
    }
}

impl Drop for Sequence {
    fn drop(&mut self) {
        if std::thread::panicking() {
            eprintln!(
                "generated inputs: seed {:#x}, failure after {} values were drawn",
                self.seed, self.drawn
            );
        }
    }
}

/// Runs one generated case; if it panics, reports `label`, the index or the
/// inputs that identify the case, before the panic continues.
pub fn case(label: impl fmt::Display, check: impl FnOnce()) {
    struct Report<L: fmt::Display>(L);

    impl<L: fmt::Display> Drop for Report<L> {
        fn drop(&mut self) {
            if std::thread::panicking() {
                eprintln!("generated case failed: {}", self.0);
            }
        }
    }

    let _report = Report(label);
    check();
}
