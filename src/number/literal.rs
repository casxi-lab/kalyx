//! Decimal literals: `digits` or `digits.digits`, read exactly.

use num_bigint::BigInt;
use num_traits::{One, Pow};

use super::arithmetic::{Parts, internal, reduce};
use crate::{Context, Error, FaultKind, LimitField, Result, Span};

/// The bits reserved per decimal digit: $10^D - 1 \lt 16^D$, so a literal of
/// $D$ digits has a numerator and a denominator of at most $4 D$ bits.
const BITS_PER_DIGIT: u64 = 4;

/// Where the scan of a literal stands.
#[derive(Clone, Copy, PartialEq, Eq)]
enum LiteralState {
    /// No digit yet.
    Start,
    /// In the digits before the point.
    Integer,
    /// Right after the point.
    Point,
    /// In the digits after the point.
    Fraction,
}

/// The span of `length` bytes at `start`, shifted by `offset`.
fn span_at(offset: usize, start: usize, length: usize) -> Option<Span> {
    let start = offset.saturating_add(start);
    Span::new(start, start.saturating_add(length))
}

/// The syntax error of a literal at `span`.
fn syntax(span: Option<Span>, message: &str) -> Error {
    Error::new(FaultKind::Syntax, span, message)
}

/// Scans `text` as `digit+ ('.' digit+)?` and returns the number of digits
/// and the position of the point; allocates and charges nothing.
fn scan(text: &str, offset: usize) -> Result<(u64, Option<usize>)> {
    let mut state = LiteralState::Start;
    let mut point = None;
    let mut digits: u64 = 0;
    for (index, character) in text.char_indices() {
        state = match (state, character) {
            (LiteralState::Start | LiteralState::Integer, '0'..='9') => LiteralState::Integer,
            (LiteralState::Point | LiteralState::Fraction, '0'..='9') => LiteralState::Fraction,
            (LiteralState::Integer, '.') => {
                point = Some(index);
                LiteralState::Point
            }
            _ => {
                let span = span_at(offset, index, character.len_utf8());
                return Err(syntax(span, "a decimal literal has the form 1 or 1.5"));
            }
        };
        if state != LiteralState::Point {
            digits = digits.saturating_add(1);
        }
    }
    match state {
        LiteralState::Integer | LiteralState::Fraction => Ok((digits, point)),
        LiteralState::Start => Err(syntax(
            span_at(offset, text.len(), 0),
            "a decimal literal needs a digit",
        )),
        LiteralState::Point => Err(syntax(
            span_at(offset, text.len(), 0),
            "a decimal point needs a digit after it",
        )),
    }
}

/// The integer of a nonempty string of ASCII digits.
fn digits_value(digits: &[u8]) -> Result<BigInt> {
    // A literal of up to 39 digits is tried as a u128, which avoids the digit
    // buffer of the general conversion.
    if digits.len() <= 39
        && let Some(value) = small_value(digits)
    {
        return Ok(BigInt::from(value));
    }
    match BigInt::parse_bytes(digits, 10) {
        Some(value) => Ok(value),
        None => Err(internal(None, "a scanned literal is not a decimal integer")),
    }
}

/// The value of at most 39 ASCII digits as a `u128`, or `None` when it does
/// not fit.
fn small_value(digits: &[u8]) -> Option<u128> {
    let mut value: u128 = 0;
    let mut index = 0;
    while index < digits.len() {
        let digit = digits[index].checked_sub(b'0')?;
        value = value.checked_mul(10)?.checked_add(u128::from(digit))?;
        index += 1;
    }
    Some(value)
}

/// The canonical parts of the decimal literal `text`, whose bytes start at
/// byte `offset` of the request's source.
///
/// Scans the literal first, then checks the bound of $4 D$ bits for its $D$
/// digits, leading zeros included, against `max_integer_bits`, then charges
/// $D$ work units, and only then converts: the digits as an integer over
/// $10^k$ for $k$ digits after the point, reduced. A syntax error carries the
/// span of the offending text, an empty span at the end for a missing digit;
/// a limit carries the span of the whole literal.
///
/// # Errors
///
/// `Syntax` for text that is not a literal; `ResourceLimit` with
/// `LimitField::IntegerBits` when $4 D$ exceeds `max_integer_bits`, and the
/// request failures of the charge.
pub(crate) fn literal(text: &str, offset: usize, context: &mut Context) -> Result<Parts> {
    let (digits, point) = scan(text, offset)?;
    let span = span_at(offset, 0, text.len());
    context.check_at(
        LimitField::IntegerBits,
        digits.saturating_mul(BITS_PER_DIGIT),
        span,
    )?;
    context.charge_at(digits, span)?;
    let parts = match point {
        None => (digits_value(text.as_bytes())?, BigInt::one()),
        Some(_) => match text.split_once('.') {
            Some((integer, fraction)) => {
                let mut all = Vec::with_capacity(text.len());
                all.extend_from_slice(integer.as_bytes());
                all.extend_from_slice(fraction.as_bytes());
                let numerator = digits_value(&all)?;
                let denominator = Pow::pow(BigInt::from(10_u8), fraction.len());
                reduce(numerator, denominator)?
            }
            None => return Err(internal(span, "a scanned literal lost its point")),
        },
    };
    Ok(parts)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::CancelFlag;
    use crate::{ErrorKind, Limits};

    #[test]
    fn a_literal_inside_a_larger_source_reports_shifted_spans() {
        let mut context = Context::new(Limits::new(), CancelFlag::new());
        let error = literal("1.x", 10, &mut context).unwrap_err();
        assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Syntax));
        assert_eq!(error.span(), Span::new(12, 13));
        let error = literal("12.", 10, &mut context).unwrap_err();
        assert_eq!(error.span(), Span::new(13, 13));
        let mut narrow = Context::new(Limits::new().with_max_integer_bits(7), CancelFlag::new());
        let error = literal("1.5", 10, &mut narrow).unwrap_err();
        assert_eq!(error.kind(), ErrorKind::ResourceLimit);
        assert_eq!(error.span(), Span::new(10, 13));
        assert_eq!(
            literal("1.50", 10, &mut context).unwrap(),
            (3.into(), 2.into())
        );
        assert_eq!(context.work_used(), 3);
    }

    #[test]
    fn small_and_large_digit_strings_convert_alike() {
        for digits in [
            "0",
            "7",
            "18446744073709551616",
            "999999999999999999999999999999999999999",
        ] {
            let small = digits_value(digits.as_bytes()).unwrap();
            assert_eq!(Some(small), BigInt::parse_bytes(digits.as_bytes(), 10));
        }
        let long = "1".repeat(40);
        assert_eq!(small_value(long.as_bytes()), None);
        assert_eq!(
            digits_value(long.as_bytes()).unwrap(),
            BigInt::parse_bytes(long.as_bytes(), 10).unwrap()
        );
    }
}
