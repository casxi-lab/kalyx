//! Integer exponents: their checks, their exact arithmetic and the merge
//! condition of powers.
//!
//! An exponent is an `i64`. Its magnitude is checked against `max_exponent`
//! and against the width of `i64`, so the effective bound is the smaller of
//! `max_exponent` and $2^{63} - 1$, and an excess names `max_exponent` with
//! that effective value as `allowed`. Sums and products of two exponents are
//! computed exactly as `i128` and checked before they become an exponent
//! again; the magnitudes are computed with bound checks and `as` conversions.

use crate::number::Integer;
use crate::{Context, LimitField, Result, Span};

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

/// The integer `value` as an exponent: its magnitude is checked against
/// `max_exponent` and the width of `i64`, as every exponent of a term is,
/// with `span` on the error; charges nothing. The parser reads the exponent
/// of a power through it.
pub(crate) fn integer_exponent(
    value: &Integer,
    span: Option<Span>,
    context: &Context,
) -> Result<i64> {
    let magnitude = value.magnitude_u64();
    context.check_width_at(LimitField::Exponent, EXPONENT_WIDTH, magnitude, span)?;
    signed(magnitude, value.is_negative())
}

/// The exponent with the admitted magnitude `magnitude` and the given sign.
fn signed(magnitude: Option<u64>, negative: bool) -> Result<i64> {
    match magnitude {
        Some(magnitude) => {
            if magnitude > EXPONENT_WIDTH {
                return Err(internal("an exponent beyond the width of i64 was admitted"));
            }
            // At most i64::MAX, so the cast and the negation are exact.
            let exponent = magnitude as i64;
            if negative {
                Ok(-exponent)
            } else {
                Ok(exponent)
            }
        }
        None => Err(internal("an exponent beyond the width of u64 was admitted")),
    }
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

    // An integer read as an exponent passes the check of every exponent:
    // `max_exponent` and the width of `i64`, with the caller's span; a
    // magnitude beyond a `u64` is reported as a bound.
    #[test]
    fn integers_become_exponents_under_the_same_check() {
        use crate::context::CancelFlag;
        use crate::number::Rational;
        use crate::{ErrorKind, LimitAmount, LimitId, Limits};

        let span = Span::new(2, 5);
        let wide = Context::new(Limits::new().with_max_exponent(u64::MAX), CancelFlag::new());
        let read = |value: &Integer| integer_exponent(value, span, &wide);
        assert_eq!(read(&Integer::from(-3_i64)).unwrap(), -3);
        assert_eq!(read(&Integer::from(0_i64)).unwrap(), 0);
        assert_eq!(read(&Integer::from(i64::MAX)).unwrap(), i64::MAX);
        let rejected = |value: &Integer, allowed: u64, amount: LimitAmount, context: &Context| {
            let error = integer_exponent(value, span, context).unwrap_err();
            assert_eq!(error.kind(), ErrorKind::ResourceLimit);
            assert_eq!(error.span(), span);
            let exceeded = error.exceeded().unwrap();
            assert_eq!(exceeded.id(), &LimitId::Field(LimitField::Exponent));
            assert_eq!(exceeded.allowed(), allowed);
            assert_eq!(exceeded.amount(), amount);
        };
        let beyond = LimitAmount::Required(EXPONENT_WIDTH + 1);
        rejected(
            &Integer::from(EXPONENT_WIDTH + 1),
            EXPONENT_WIDTH,
            beyond,
            &wide,
        );
        rejected(&Integer::from(i64::MIN), EXPONENT_WIDTH, beyond, &wide);
        let mut scratch = Context::new(Limits::new(), CancelFlag::new());
        let two = Rational::from(2_i64);
        let huge = two.power(64, &mut scratch).unwrap();
        let bound = LimitAmount::Bound(u64::MAX);
        rejected(huge.numerator(), EXPONENT_WIDTH, bound, &wide);
        let default = Context::new(Limits::new(), CancelFlag::new());
        assert_eq!(
            integer_exponent(&Integer::from(-4096_i64), span, &default).unwrap(),
            -4096
        );
        let over = LimitAmount::Required(4097);
        rejected(&Integer::from(4097_i64), 4096, over, &default);
    }
}
