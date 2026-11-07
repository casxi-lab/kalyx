//! Integer exponents: their checks, their exact arithmetic and the merge
//! condition of powers.
//!
//! An exponent is an `i64`. Its magnitude is checked against `max_exponent`
//! and against the width of `i64`, so the effective bound is the smaller of
//! `max_exponent` and $2^{63} - 1$, and an excess names `max_exponent` with
//! that effective value as `allowed`. Sums and products of two exponents are
//! computed exactly as `i128` and checked before they become an exponent
//! again; the magnitudes are computed with bound checks and `as` conversions.

use crate::{Context, LimitField, Result};

use super::node::internal;

/// The largest magnitude of an exponent that a term holds: the largest
/// `i64`. It is the machine width that bounds `max_exponent` for terms.
pub(super) const EXPONENT_WIDTH: u64 = i64::MAX as u64;

/// The magnitude $\lvert k \rvert$ of the exponent `exponent`.
pub(super) const fn magnitude(exponent: i64) -> u64 {
    if exponent < 0 {
        // -(exponent + 1) is at most i64::MAX, so neither step overflows.
        ((-(exponent + 1)) as u64) + 1
    } else {
        exponent as u64
    }
}

/// Checks the exponent `exponent` against `max_exponent` and the width of
/// `i64`; charges nothing.
pub(super) fn check(exponent: i64, context: &Context) -> Result<()> {
    context.check_width_at(
        LimitField::Exponent,
        EXPONENT_WIDTH,
        Some(magnitude(exponent)),
        None,
    )
}

/// The sum `left + right` of two exponents, checked as an exponent.
pub(super) fn sum(left: i64, right: i64, context: &Context) -> Result<i64> {
    exact((left as i128) + (right as i128), context)
}

/// The product `left * right` of two exponents, checked as an exponent.
pub(super) fn product(left: i64, right: i64, context: &Context) -> Result<i64> {
    // The magnitudes are at most 2^63, so the product is at most 2^126.
    exact((left as i128) * (right as i128), context)
}

/// The exact value `value`, of magnitude at most $2^{126}$, as an exponent:
/// checked against `max_exponent` and the width of `i64`.
fn exact(value: i128, context: &Context) -> Result<i64> {
    let magnitude: u128 = if value < 0 {
        (-value) as u128
    } else {
        value as u128
    };
    let amount = if magnitude > (u64::MAX as u128) {
        None
    } else {
        Some(magnitude as u64)
    };
    context.check_width_at(LimitField::Exponent, EXPONENT_WIDTH, amount, None)?;
    if magnitude > (EXPONENT_WIDTH as u128) {
        return Err(internal("an exponent beyond the width of i64 was admitted"));
    }
    Ok(value as i64)
}

/// Whether the power of a power $(b^j)^k$ becomes $b^{jk}$: when
/// $jk \lt 0$, when $j, k \ge 0$, or when $j = 0$. Otherwise the result
/// would no longer show a base that occurs with a negative exponent, and the
/// power is kept as it is.
pub(super) const fn mergeable(inner: i64, outer: i64) -> bool {
    inner == 0 || (inner < 0 && outer > 0) || (inner > 0 && outer < 0) || (inner >= 0 && outer >= 0)
}

/// The logical bytes of the exponent `exponent` written as a number:
/// $\lvert k \rvert + 4$, the cost $\lvert k \rvert + \lvert 1 \rvert + 3$ of
/// the rational $k / 1$, with $\lvert k \rvert$ the bit length of its
/// magnitude.
pub(super) const fn rendered_bytes(exponent: i64) -> u64 {
    bit_length(magnitude(exponent)) + 4
}

/// The bit length of `value`: 0 for zero, otherwise
/// $\lfloor \log_2 v \rfloor + 1$.
const fn bit_length(value: u64) -> u64 {
    let mut rest = value;
    let mut bits = 0;
    while rest > 0 {
        rest >>= 1;
        bits += 1;
    }
    bits
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn magnitudes_cover_the_whole_range_of_i64() {
        assert_eq!(magnitude(0), 0);
        assert_eq!(magnitude(-1), 1);
        assert_eq!(magnitude(i64::MAX), EXPONENT_WIDTH);
        assert_eq!(magnitude(i64::MIN), EXPONENT_WIDTH + 1);
    }

    #[test]
    fn the_merge_condition_never_hides_a_negative_exponent() {
        // jk < 0, j, k >= 0 and j = 0 merge; two negative exponents do not.
        assert!(mergeable(-1, 2));
        assert!(mergeable(2, -1));
        assert!(mergeable(2, 3));
        assert!(mergeable(0, -5));
        assert!(!mergeable(-1, -1));
        assert!(!mergeable(-2, -3));
    }

    #[test]
    fn exponents_are_written_as_rationals() {
        assert_eq!(rendered_bytes(0), 4);
        assert_eq!(rendered_bytes(1), 5);
        assert_eq!(rendered_bytes(-1), 5);
        assert_eq!(rendered_bytes(2), 6);
        assert_eq!(rendered_bytes(4096), 17);
        assert_eq!(rendered_bytes(i64::MIN), 68);
    }
}
