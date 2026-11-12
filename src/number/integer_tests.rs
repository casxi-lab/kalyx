//! Unit tests of the integer kernel that compare it with num-bigint
//! directly: operands of 150 bits and more, built from the digits of a
//! seeded sequence, and models of Euclid's algorithm and of repeated
//! multiplication written here over `BigInt`. The integration tests in
//! `tests/integers.rs` check the kernel through the public interface alone.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use super::{
    Congruence, CrtResult, Integer, ModularInverse, crt, extended_gcd, gcd, lcm, modular_inverse,
    modular_power,
};
use crate::context::CancelFlag;
use crate::{Context, ErrorKind, FaultKind, Limits};

/// A fixed linear congruential sequence for reproducible generated inputs.
///
/// When a test panics while a sequence is alive, the sequence reports its
/// seed and how many values it produced, which identify the generated case
/// that failed.
struct Sequence {
    seed: u64,
    state: u64,
    drawn: u64,
}

impl Sequence {
    fn new(seed: u64) -> Self {
        Self {
            seed,
            state: seed,
            drawn: 0,
        }
    }

    /// The next value, uniformly in `low..=high` up to the generator's bias.
    fn next_in(&mut self, low: i64, high: i64) -> i64 {
        self.state = self
            .state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.drawn += 1;
        let span = (high - low + 1) as u64;
        low + ((self.state >> 33) % span) as i64
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

/// A context with default limits and a work budget of 100,000,000 units.
fn c() -> Context {
    Context::new(Limits::new().with_max_work(100_000_000), CancelFlag::new())
}

fn b(n: i64) -> BigInt {
    BigInt::from(n)
}

fn z(n: &BigInt) -> Integer {
    Integer(n.clone())
}

/// The GCD of machine integers by Euclid's algorithm.
fn small_gcd(mut a: i64, mut b: i64) -> i64 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// Euclid's algorithm on the absolute values of arbitrary integers.
fn euclid(a: &BigInt, d: &BigInt) -> BigInt {
    let (mut a, mut d) = (a.abs(), d.abs());
    while !d.is_zero() {
        let remainder = &a % &d;
        a = std::mem::replace(&mut d, remainder);
    }
    a
}

/// `bits` random bits from the sequence in chunks of at most 26 bits, the
/// most significant chunk first.
fn seeded_bits(sequence: &mut Sequence, bits: u32) -> BigInt {
    let mut value = BigInt::zero();
    let mut filled = 0;
    while filled < bits {
        let chunk = (bits - filled).min(26);
        value = (value << chunk) + sequence.next_in(0, (1 << chunk) - 1);
        filled += chunk;
    }
    value
}

// Carried over: the GCD, the Bézout coefficients and the LCM of every pair
// of operands in -22..=22 against a machine-integer model, and the Bézout
// identity of a pair of 1,000-bit operands.
#[test]
fn bezout_and_lcm_all_signs_and_zeros() {
    for a in -22..=22 {
        for d in -22..=22 {
            let g = small_gcd(a, d);
            assert_eq!(gcd(&z(&b(a)), &z(&b(d)), &mut c()).unwrap(), z(&b(g)));
            let r = extended_gcd(&z(&b(a)), &z(&b(d)), &mut c()).unwrap();
            assert_eq!(r.gcd(), &z(&b(g)));
            assert_eq!(&r.left().0 * b(a) + &r.right().0 * b(d), b(g));
            let l = if g == 0 { 0 } else { (a / g * d).abs() };
            assert_eq!(lcm(&z(&b(a)), &z(&b(d)), &mut c()).unwrap(), z(&b(l)));
        }
    }
    let n = BigInt::one() << 1000_usize;
    let (left, right) = (&n + 17, &n - 19);
    let r = extended_gcd(&z(&left), &z(&right), &mut c()).unwrap();
    assert_eq!(&r.left().0 * &left + &r.right().0 * &right, r.gcd().0);
}

// Carried over: signed operands below 2^150 in absolute value; every other
// pair shares a random factor below 2^60 so that the GCD is large. The GCD
// comes from Euclid's algorithm here, `g = s*a + t*b` makes it the greatest
// common divisor, and `lcm*gcd = |a*b|`.
#[test]
fn gcd_lcm_and_bezout_hold_for_seeded_150_bit_operands() {
    let mut sequence = Sequence::new(150);
    let mut context = c();
    for case in 0..80 {
        let operand = |sequence: &mut Sequence| {
            let magnitude = seeded_bits(sequence, 150);
            if sequence.next_in(0, 1) == 0 {
                -magnitude
            } else {
                magnitude
            }
        };
        let (mut a, mut d) = (operand(&mut sequence), operand(&mut sequence));
        if case % 2 == 0 {
            let shared = seeded_bits(&mut sequence, 60) + 1;
            a *= &shared;
            d *= &shared;
        }
        let g = euclid(&a, &d);
        assert_eq!(gcd(&z(&a), &z(&d), &mut context).unwrap().0, g, "{a}, {d}");
        let bezout = extended_gcd(&z(&a), &z(&d), &mut context).unwrap();
        assert_eq!(bezout.gcd().0, g);
        assert_eq!(&bezout.left().0 * &a + &bezout.right().0 * &d, g);
        let l = lcm(&z(&a), &z(&d), &mut context).unwrap().0;
        assert_eq!(&l * &g, (&a * &d).abs(), "{a}, {d}");
        assert!((&l % &a).is_zero() && (&l % &d).is_zero());
    }
}

// Carried over: bases below 2^120 in absolute value, moduli in 1..2^80 and
// exponents in -50..200. Nonnegative powers are compared with repeated
// multiplication; a negative power `r` must satisfy `r*a^|e| = 1`, and an
// inverse `v` must satisfy `v*a = 1` modulo `m`. Without `gcd(a, m) = 1`
// there is no inverse, the non-unit carries `gcd(a mod m, m)`, and a
// negative power is `OutsideDomain`.
#[test]
fn modular_powers_and_inverses_match_repeated_multiplication() {
    let mut sequence = Sequence::new(80);
    let mut context = c();
    let one = |m: &BigInt| BigInt::one() % m;
    for _ in 0..100 {
        let magnitude = seeded_bits(&mut sequence, 120);
        let a = if sequence.next_in(0, 1) == 0 {
            -magnitude
        } else {
            magnitude
        };
        let m = seeded_bits(&mut sequence, 80).max(b(1));
        let e = sequence.next_in(-50, 199);
        let residue = (&a % &m + &m) % &m;
        let mut power = one(&m);
        for _ in 0..e.unsigned_abs() {
            power = power * &residue % &m;
        }
        let invertible = euclid(&a, &m).is_one();
        match modular_inverse(&z(&a), &z(&m), &mut context).unwrap() {
            ModularInverse::Inverse(inverse) => {
                assert!(invertible, "{a} mod {m}");
                assert!(inverse.0 >= BigInt::zero() && inverse.0 < m);
                assert_eq!(inverse.0 * &residue % &m, one(&m));
            }
            ModularInverse::NonUnit(divisor) => {
                assert!(!invertible, "{a} mod {m}");
                assert_eq!(divisor.0, euclid(&residue, &m), "{a} mod {m}");
            }
        }
        let result = modular_power(&z(&a), &z(&b(e)), &z(&m), &mut context);
        if e >= 0 {
            assert_eq!(result.unwrap().0, power, "{a}^{e} mod {m}");
        } else if invertible {
            let result = result.unwrap().0;
            assert!(result >= BigInt::zero() && result < m);
            assert_eq!(result * &power % &m, one(&m), "{a}^{e} mod {m}");
        } else {
            assert_eq!(
                result.unwrap_err().kind(),
                ErrorKind::Fault(FaultKind::OutsideDomain)
            );
        }
    }
}

// Carried over: systems of one to four congruences with moduli in 1..=16
// and residues in -20..20, compared with a search over one period of the
// moduli's least common multiple.
#[test]
fn crt_systems_of_up_to_four_congruences_match_brute_force() {
    let mut sequence = Sequence::new(16);
    let mut context = c();
    let mut inconsistent = 0;
    for _ in 0..100 {
        let count = sequence.next_in(1, 4);
        let system: Vec<(i64, i64)> = (0..count)
            .map(|_| (sequence.next_in(-20, 19), sequence.next_in(1, 16)))
            .collect();
        let period = system.iter().fold(1, |l, &(_, m)| l / small_gcd(l, m) * m);
        let expected =
            (0..period).find(|x| system.iter().all(|&(r, m)| (x - r).rem_euclid(m) == 0));
        let inputs: Vec<_> = system
            .iter()
            .map(|&(r, m)| Congruence::new(&z(&b(r)), &z(&b(m)), &mut context).unwrap())
            .collect();
        let result = crt(&inputs, &mut context).unwrap();
        let found = match result {
            CrtResult::Solution(solution) => {
                Some((solution.residue().0.clone(), solution.modulus().0.clone()))
            }
            CrtResult::Inconsistent => None,
        };
        assert_eq!(found, expected.map(|x| (b(x), b(period))), "{system:?}");
        inconsistent += usize::from(expected.is_none());
    }
    assert!(inconsistent > 0);
}
