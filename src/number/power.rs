//! Integer powers: the bit bound of a power, checked before any charge, the
//! charge of a power by the machine words of the operands of its steps, made
//! once before it is computed, and binary powering of one part.
//!
//! The bound is computed from the operands with machine integers only, and
//! without allocating: an upper bound of $\log_2$ of the leading 64 bits of
//! the base, in fixed point with 32 fractional bits, scaled by the exponent,
//! and capped by the estimate $m \lvert x \rvert + 1$. It is exact for a power
//! of two, never above the estimate, and at most one bit above the bit length
//! of the power for exponents below $2^{31}$, so for those exponents the check
//! rejects only powers that are larger than the limit or within one bit of it.

use num_bigint::{BigInt, BigUint};
use num_traits::{One, ToPrimitive};

use super::words;

/// The fractional bits of the fixed-point logarithm.
const FRACTION_BITS: u32 = 32;

/// The fractional bits of the mantissa while the logarithm is computed: a
/// mantissa in $[1, 2]$ is held as an integer in $[2^{62}, 2^{63}]$, so its
/// square fits in a `u128`.
const MANTISSA_BITS: u32 = 62;

/// $\lceil x / 2^k \rceil$.
const fn ceil_shift(x: u128, k: u32) -> u128 {
    let quotient = x >> k;
    if quotient << k == x {
        quotient
    } else {
        quotient + 1
    }
}

/// An upper bound $L$ of $\log_2 u$ in fixed point: $\log_2 u \le L / 2^{32}$,
/// for $1 \le u \le 2^{64}$.
///
/// With $e = \lfloor \log_2 u \rfloor$ and the mantissa $y = u / 2^e$, each step
/// squares the mantissa, rounded up, and takes one bit of $\log_2 y$: the bit
/// is 1 when the square reaches 2, which is then halved, rounded up. Rounding
/// up keeps $\log_2 y \le (B_k + \log_2 z_k) / 2^k$ for the bits $B_k$ and the
/// mantissa $z_k \in [1, 2]$ after $k$ steps, so $L = 2^{32} e + B_{32} + 1$,
/// or $2^{32} e + B_{32}$ when $z_{32} = 1$; for a power of two $u$ the mantissa
/// stays 1 and $L = 2^{32} e$ is exact.
const fn log2_upper(u: u128) -> u128 {
    // u >= 1, so e is at most 127.
    let e = 127_u32.saturating_sub(u.leading_zeros());
    let two = 1_u128 << (MANTISSA_BITS + 1);
    // u < 2^65, so u 2^62 < 2^127.
    let mut z = ceil_shift(u << MANTISSA_BITS, e);
    let mut bits: u128 = 0;
    let mut step = 0;
    while step < FRACTION_BITS {
        // z <= 2^63, so z^2 <= 2^126.
        z = ceil_shift(z * z, MANTISSA_BITS);
        bits <<= 1;
        if z >= two {
            bits |= 1;
            z = ceil_shift(z, 1);
        }
        step += 1;
    }
    // log2 z_32 is 0 when z_32 = 1 and at most 1 otherwise.
    let last = if z > (1_u128 << MANTISSA_BITS) { 1 } else { 0 };
    ((e as u128) << FRACTION_BITS) + bits + last
}

/// $(u, s)$ with $x \le u \cdot 2^s$ for a nonzero $x$ of `length` bits: $x$
/// itself and $s = 0$ when it has at most 64 bits, and otherwise its leading
/// 64 bits, plus one unless the $s$ bits below them are all zero. Reads the
/// digits of $x$ without allocating; `None` only if the digits contradict
/// `length`.
fn leading_word(x: &BigUint, length: u64) -> Option<(u128, u64)> {
    if length <= 64 {
        let value = x.to_u64()?;
        return Some((u128::from(value), 0));
    }
    let s = length - 64;
    let mut digits = x.iter_u64_digits().rev();
    let (high, low) = match (digits.next(), digits.next()) {
        (Some(high), Some(low)) => (high, low),
        _ => return None,
    };
    // The top digit holds the leading `t` bits, 1 <= t <= 64.
    let t = length % 64;
    let top = if t == 0 {
        high
    } else {
        (high << (64 - t)) | (low >> t)
    };
    let exact = match x.trailing_zeros() {
        Some(zeros) => zeros >= s,
        None => true,
    };
    let u = if exact {
        u128::from(top)
    } else {
        u128::from(top) + 1
    };
    Some((u, s))
}

/// An upper bound of the bit length of $x^m$, from the bit length and the
/// leading 64 bits of $x$; 1 for $m = 0$, since $x^0 = 1$, and 0 for $x = 0$
/// and $m \ge 1$. `None` when the bound does not fit in a `u64`.
///
/// With $x \le u \cdot 2^s$ from `leading_word`, the bit length of $x^m$ is at
/// most $\lfloor m L / 2^{32} \rfloor + m s + 1$ for $L = $ `log2_upper(u)`,
/// and at most $m \lvert x \rvert$ since $x \lt 2^{\lvert x \rvert}$; the bound
/// is the smaller of the first and $m \lvert x \rvert + 1$.
pub(crate) fn power_bits(x: &BigUint, m: u64) -> Option<u64> {
    if m == 0 {
        return Some(1);
    }
    let length = x.bits();
    if length == 0 {
        return Some(0);
    }
    let (u, s) = leading_word(x, length)?;
    let m = u128::from(m);
    // m < 2^64 and L < 2^39, so m L < 2^103; m s < 2^128.
    let scaled = (m * log2_upper(u)) >> FRACTION_BITS;
    let bound = scaled
        .saturating_add(m.saturating_mul(u128::from(s)))
        .saturating_add(1);
    // m |x| <= (2^64 - 1)^2, so the estimate does not overflow.
    let estimate = m * u128::from(length) + 1;
    let bound = if bound < estimate { bound } else { estimate };
    u64::try_from(bound).ok()
}

/// The machine words of the operand $x^j$ of a step of binary powering of a
/// rational $x$ with the parts `numerator` and `denominator`: the words of
/// the larger of the bounds $P$ of the bits of its parts, and those of
/// `u64::MAX` bits when a bound does not fit in a `u64`, which the check of
/// the bound of the power rejects first.
fn operand_words(numerator: &BigUint, denominator: &BigUint, j: u64) -> u64 {
    match (power_bits(numerator, j), power_bits(denominator, j)) {
        (Some(n), Some(d)) => words(if n < d { d } else { n }),
        _ => words(u64::MAX),
    }
}

/// The work charged for the power $x^m$ of a rational $x$ with the parts
/// `numerator` and `denominator`, before it is computed: one unit, one more
/// for $m \ge 1$, and the steps of binary powering by the machine words of
/// their operands, saturating at `u64::MAX`.
///
/// Binary powering reads the bits of $m$ from the lowest: at bit $i$, when
/// it is set, it multiplies the power $x^{m \bmod 2^i}$ computed so far by
/// $x^{2^i}$, for $W(x^{m \bmod 2^i}) W(x^{2^i})$ units, and below the
/// highest bit it squares $x^{2^i}$, for $W(x^{2^i})^2$ units, where $W$ is
/// `operand_words`. A step on a rational squares or multiplies both its
/// numerator and its denominator, so it costs at most twice what it is
/// charged. When the bound of every operand is at most 64 bits, every step
/// charges one unit, and the charge is $1 + \lvert m \rvert + w(m)$ for the
/// bit length $\lvert m \rvert$ and the number $w(m)$ of one bits of $m$:
/// one unit, one more, $\lvert m \rvert - 1$ squarings and $w(m)$
/// multiplications.
pub(crate) fn power_charge(numerator: &BigUint, denominator: &BigUint, m: u64) -> u64 {
    let length = u64::from(u64::BITS - m.leading_zeros());
    let mut charge: u64 = if m == 0 { 1 } else { 2 };
    let mut bit = 0;
    while bit < length {
        // bit < 64, since m has at most 64 bits.
        let square = 1_u64 << bit;
        if (m >> bit) & 1 == 1 {
            let below = m & (square - 1);
            let product = operand_words(numerator, denominator, below)
                .saturating_mul(operand_words(numerator, denominator, square));
            charge = charge.saturating_add(product);
        }
        bit += 1;
        if bit < length {
            let operand = operand_words(numerator, denominator, square);
            charge = charge.saturating_add(operand.saturating_mul(operand));
        }
    }
    charge
}

/// $x^m$ by binary powering, with $x^0 = 1$. Every intermediate value is a
/// power $x^j$ with $j \le m$, so the bit bound of the result bounds it.
pub(crate) fn power_part(x: BigInt, m: u64) -> BigInt {
    let mut result = BigInt::one();
    let mut base = x;
    let mut exponent = m;
    while exponent != 0 {
        if exponent & 1 == 1 {
            result *= &base;
        }
        exponent >>= 1;
        if exponent != 0 {
            base = &base * &base;
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_power_bound_is_exact_within_one_bit() {
        for x in 0_u64..=300 {
            let base = BigUint::from(x);
            for m in 0_u64..=200 {
                let actual = BigInt::from(x).pow(u32::try_from(m).unwrap()).bits();
                let bound = power_bits(&base, m).unwrap();
                assert!(actual <= bound, "{x}^{m}: {actual} > {bound}");
                assert!(bound <= actual + 1, "{x}^{m}: {bound} > {actual} + 1");
            }
        }
    }

    #[test]
    fn the_power_bound_is_exact_for_powers_of_two_and_holds_for_wide_bases() {
        for k in [0_u64, 1, 5, 63, 64, 65, 200] {
            let base = BigUint::one() << k;
            for m in [1_u64, 2, 3, 100, 4095] {
                assert_eq!(power_bits(&base, m), Some(k * m + 1), "2^{k} to the {m}");
            }
        }
        let wide = (BigUint::one() << 300_u32) - 1_u32;
        for m in [1_u64, 2, 7, 33] {
            let actual = BigInt::from(wide.clone())
                .pow(u32::try_from(m).unwrap())
                .bits();
            let bound = power_bits(&wide, m).unwrap();
            assert!(
                actual <= bound && bound <= actual + 1,
                "{m}: {actual} {bound}"
            );
        }
        assert_eq!(power_bits(&BigUint::from(3_u8), u64::MAX), None);
    }

    #[test]
    fn the_power_bound_holds_its_claims_for_large_exponents() {
        // Exact for powers of two, of every width, beyond 2^32.
        for k in [0_u64, 1, 2, 63, 64, 65, 127, 128, 200] {
            let base = BigUint::one() << k;
            for m in [1_u64 << 32, (1 << 32) + 1, 1 << 40, (1 << 50) + 3] {
                assert_eq!(power_bits(&base, m), Some(k * m + 1), "2^{k} to the {m}");
            }
        }
        assert_eq!(power_bits(&BigUint::one(), u64::MAX), Some(1));
        // Never above the estimate m |x| + 1, even when the leading 64 bits
        // are all ones and the leading word rounds up to 2^64.
        for length in [3_u32, 64, 65, 66, 128, 129, 300] {
            let all_ones = (BigUint::one() << length) - 1_u32;
            let low_one = (BigUint::one() << (length - 1)) + 1_u32;
            for base in [all_ones, low_one] {
                for m in [1_u64, 2, 4095, 1 << 32, 1 << 40, 1 << 50] {
                    let estimate = m * u64::from(length) + 1;
                    let bound = power_bits(&base, m).unwrap();
                    assert!(bound <= estimate, "{base} to the {m}: {bound} > {estimate}");
                    assert!(bound > m * u64::from(length - 1), "{base} to the {m}");
                }
            }
        }
        // A wide base whose low bits are zero is bounded as exactly as its
        // leading word.
        let shifted = BigUint::from(3_u8) << 100_u32;
        for m in [1_u64, 2, 7, 33] {
            let actual = BigInt::from(shifted.clone())
                .pow(u32::try_from(m).unwrap())
                .bits();
            let bound = power_bits(&shifted, m).unwrap();
            assert!(
                actual <= bound && bound <= actual + 1,
                "{m}: {actual} {bound}"
            );
        }
    }

    #[test]
    fn the_power_bound_holds_where_the_last_unit_of_the_logarithm_decides() {
        // m log2 x lies less than m / 2^32 above an integer.
        for (x, m) in [(153_u32, 6_531_u32), (11, 16_503)] {
            let actual = BigInt::from(x).pow(m).bits();
            let bound = power_bits(&BigUint::from(x), u64::from(m)).unwrap();
            assert!(
                actual <= bound && bound <= actual + 1,
                "{x}^{m}: {actual} {bound}"
            );
        }
    }

    #[test]
    fn the_power_bound_can_be_two_bits_above_just_below_2_pow_32() {
        // u^m with m = 2^32 - 1 has 64 m - 1 = 274877906879 bits, since
        // m ln(2^64 / u) lies between ln 2 and 2 ln 2.
        let u = 18_446_744_070_732_507_143_u64;
        assert_eq!(
            power_bits(&BigUint::from(u), (1 << 32) - 1),
            Some(274_877_906_881)
        );
    }

    #[test]
    fn binary_powering_matches_repeated_products() {
        for x in [-7_i64, -2, -1, 0, 1, 2, 3, 10] {
            let mut expected = BigInt::one();
            for m in 0_u64..40 {
                assert_eq!(power_part(BigInt::from(x), m), expected, "{x}^{m}");
                expected *= x;
            }
        }
        // With one-word operands: 1 + |m| + w(m).
        let one = BigUint::one();
        assert_eq!(power_charge(&one, &one, 0), 1);
        assert_eq!(power_charge(&one, &one, 1), 3);
        assert_eq!(power_charge(&one, &one, 5), 6);
        assert_eq!(power_charge(&one, &one, 4096), 15);
    }

    /// The charge of binary powering of $n/d$ to the $m$, from the words of
    /// the bits of the operands of its steps, computed here, with `slack`
    /// bits added to each operand.
    fn stepped_charge(numerator: &BigUint, denominator: &BigUint, m: u64, slack: u64) -> u64 {
        let size = |n: &BigUint, d: &BigUint| words(n.bits().max(d.bits()) + slack);
        let mut charge = if m == 0 { 1 } else { 2 };
        let (mut power_n, mut power_d) = (BigUint::one(), BigUint::one());
        let (mut base_n, mut base_d) = (numerator.clone(), denominator.clone());
        let mut exponent = m;
        while exponent != 0 {
            if exponent & 1 == 1 {
                charge += size(&power_n, &power_d) * size(&base_n, &base_d);
                power_n *= &base_n;
                power_d *= &base_d;
            }
            exponent >>= 1;
            if exponent != 0 {
                charge += size(&base_n, &base_d).pow(2);
                base_n = &base_n * &base_n;
                base_d = &base_d * &base_d;
            }
        }
        charge
    }

    #[test]
    fn the_charge_of_a_power_counts_the_words_of_its_steps() {
        let two_to = |k: u32| BigUint::one() << k;
        let bases = [
            (BigUint::from(0_u8), BigUint::one()),
            (BigUint::one(), BigUint::one()),
            (BigUint::from(3_u8), BigUint::one()),
            (BigUint::from(2_u8), BigUint::from(3_u8)),
            (two_to(64), BigUint::one()),
            (two_to(64) - 1_u32, BigUint::from(7_u8)),
            (two_to(63) + 1_u32, two_to(70) - 1_u32),
            (BigUint::from(5_u8).pow(30), BigUint::from(7_u8).pow(20)),
            (BigUint::from(3_u8), two_to(200)),
        ];
        let exponents = (0_u64..=70).chain([100, 127, 128, 255, 300]);
        for (n, d) in &bases {
            for m in exponents.clone() {
                let charge = power_charge(n, d, m);
                // The bounds are at least the bits of every operand and at
                // most one bit above them.
                assert!(stepped_charge(n, d, m, 0) <= charge, "{n}/{d} to the {m}");
                assert!(charge <= stepped_charge(n, d, m, 1), "{n}/{d} to the {m}");
                // The order of the parts does not matter, as for a negative
                // exponent, which inverts the base.
                assert_eq!(power_charge(d, n, m), charge, "{d}/{n} to the {m}");
            }
        }
        // The bounds of powers of two are exact, so the charge is.
        for k in [1_u32, 5, 63, 64, 65, 100] {
            for m in [1_u64, 2, 3, 7, 64, 100, 129] {
                let base = two_to(k);
                assert_eq!(
                    power_charge(&base, &BigUint::one(), m),
                    stepped_charge(&base, &BigUint::one(), m, 0),
                    "2^{k} to the {m}"
                );
            }
        }
        // 2^64 to the 4: one unit, one more, the multiplication of 1 by
        // 2^256 (1 * 5 words) and the squarings of 2^64 and 2^128 (2^2 and
        // 3^2 words).
        assert_eq!(power_charge(&two_to(64), &BigUint::one(), 4), 2 + 5 + 4 + 9);
        // Saturation: the exponent u64::MAX of 3 has 64 squarings of bounds
        // beyond any word count that fits.
        assert_eq!(
            power_charge(&BigUint::from(3_u8), &BigUint::one(), u64::MAX),
            u64::MAX
        );
    }
}
