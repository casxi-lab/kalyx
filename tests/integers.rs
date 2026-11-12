//! The integer kernel through the public interface: the arithmetic of
//! `Integer`, the GCD, the LCM, the extended GCD, the modular inverse, the
//! modular power and Chinese remaindering, with their bounds, charges,
//! storage costs, domain errors and outcomes. The rules are those of
//! `docs/components/numbers/contract.md`. The tests that compare the kernel
//! with num-bigint directly are in `src/number/integer_tests.rs`.

#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    reason = "the helpers of the tests unwrap their results, as the tests do"
)]

use kalyx::context::{CancelFlag, Clock, Storage, StorageCost};
use kalyx::number::{
    self, Congruence, CrtResult, ExactQuotient, Integer, ModularInverse, Rational,
};
use kalyx::{
    Context, Error, ErrorClass, ErrorKind, FaultKind, LimitAmount, LimitField, LimitId, LimitScope,
    Limits,
};

// ---------------------------------------------------------------------------
// Helpers

fn context(limits: Limits) -> Context {
    Context::new(limits, CancelFlag::new())
}

/// A context with default limits and a work budget of 100,000,000 units.
fn c() -> Context {
    context(Limits::new().with_max_work(100_000_000))
}

/// Limits far beyond the operands of these tests, for building operands and
/// expected values with the operations of `Rational`.
fn wide() -> Context {
    context(
        Limits::new()
            .with_max_work(u64::MAX)
            .with_max_integer_bits(1 << 20)
            .with_max_exponent(1 << 20),
    )
}

fn z(n: i64) -> Integer {
    Integer::from(n)
}

/// $2^k + c$, built with the operations of `Rational`.
fn two_to_plus(k: i64, c: i64) -> Integer {
    let context = &mut wide();
    Rational::from(2_i64)
        .power(k, context)
        .unwrap()
        .add(&Rational::from(c), context)
        .unwrap()
        .numerator()
        .clone()
}

/// The integer `x` as a rational, for computing expected values with the
/// operations of `Rational`, which the kernel does not use.
fn q(x: &Integer) -> Rational {
    Rational::from(x.clone())
}

/// The value of `x`, which must have at most 127 bits, as an `i128`, read
/// from its decimal digits.
fn wide_value(x: &Integer) -> i128 {
    x.to_string().parse().unwrap()
}

/// The machine words $\max(1, \lceil \lvert x \rvert / 64 \rceil)$ of `x`.
fn words(x: &Integer) -> u64 {
    x.bits().div_ceil(64).max(1)
}

fn assert_limit(error: &Error, field: LimitField) {
    assert_eq!(error.kind(), ErrorKind::ResourceLimit, "{error}");
    let exceeded = error.exceeded().unwrap();
    assert_eq!(exceeded.id(), &LimitId::Field(field), "{error}");
}

fn assert_bits(error: &Error, required: u64) {
    assert_limit(error, LimitField::IntegerBits);
    assert_eq!(
        error.exceeded().unwrap().amount(),
        LimitAmount::Required(required),
        "{error}"
    );
}

fn assert_fault(error: &Error, fault: FaultKind) {
    assert_eq!(error.kind(), ErrorKind::Fault(fault), "{error}");
}

/// A clock that always reads the same time.
struct FixedClock(u64);

impl Clock for FixedClock {
    fn now(&mut self) -> u64 {
        self.0
    }

    fn fork(&self) -> Box<dyn Clock> {
        Box::new(FixedClock(self.0))
    }
}

/// A context under `limits` whose deadline has passed: the fixed clock reads
/// 10 and the deadline is 5.
fn expired(limits: Limits) -> Context {
    Context::with_observers(
        limits,
        Box::new(FixedClock(10)),
        Box::new(CancelFlag::new()),
    )
    .with_deadline(5)
}

/// A context under `limits` that is cancelled before its first charge.
fn cancelled(limits: Limits) -> Context {
    let flag = CancelFlag::new();
    flag.cancel();
    Context::new(limits, flag)
}

fn congruence(residue: i64, modulus: i64, context: &mut Context) -> Congruence {
    Congruence::new(&z(residue), &z(modulus), context).unwrap()
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

/// SplitMix64, a fixed-seed generator written here; the tests use no
/// external generator.
struct SplitMix64(u64);

impl SplitMix64 {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A value in `0..bound`.
    fn below(&mut self, bound: u64) -> u64 {
        self.next() % bound
    }

    /// A value in `low..=high`.
    fn between(&mut self, low: i64, high: i64) -> i64 {
        let span = u64::try_from(high - low).unwrap() + 1;
        low + i64::try_from(self.below(span)).unwrap()
    }

    /// A signed integer of at most `width` bits, at most 62: its bit length
    /// is uniform in `0..=width`, so zero, small and large values all occur.
    fn signed(&mut self, width: u32) -> i64 {
        let length = u32::try_from(self.below(u64::from(width) + 1)).unwrap();
        let magnitude = if length == 0 {
            0
        } else {
            i64::try_from(self.next() >> (64 - length)).unwrap()
        };
        if self.next() & 1 == 0 {
            magnitude
        } else {
            -magnitude
        }
    }

    /// A pair of operands below $2^{62}$ in absolute value; every other pair
    /// shares a factor below $2^{21}$.
    fn pair(&mut self, case: usize) -> (i64, i64) {
        if case.is_multiple_of(2) {
            (self.signed(62), self.signed(62))
        } else {
            let factor = self.between(1, (1 << 21) - 1);
            (self.signed(40) * factor, self.signed(40) * factor)
        }
    }
}

/// The extended Euclidean algorithm on machine integers, with the
/// coefficients that the kernel chooses: the algorithm runs on the absolute
/// values, the signs of the operands are then given to the coefficients, and
/// $(0, 0)$ gives $(0, 0, 0)$.
fn bezout_model(a: i128, b: i128) -> (i128, i128, i128) {
    let (mut old_r, mut r) = (a.abs(), b.abs());
    let (mut old_s, mut s) = (if a == 0 && b == 0 { 0 } else { 1 }, 0);
    let (mut old_t, mut t) = (0, 1);
    while r != 0 {
        let quotient = old_r / r;
        (old_r, r) = (r, old_r - quotient * r);
        (old_s, s) = (s, old_s - quotient * s);
        (old_t, t) = (t, old_t - quotient * t);
    }
    let s = if a < 0 { -old_s } else { old_s };
    let t = if b < 0 { -old_t } else { old_t };
    (old_r, s, t)
}

/// The common solutions of a system of congruences in machine integers:
/// the residue and the modulus, or `None` when the system is inconsistent.
fn crt_model(system: &[(i128, i128)]) -> Option<(i128, i128)> {
    let (mut residue, mut modulus) = (0_i128, 1_i128);
    for &(r, m) in system {
        let r = r.rem_euclid(m);
        let (g, s, _) = bezout_model(modulus, m);
        let delta = r - residue;
        if delta % g != 0 {
            return None;
        }
        let n = m / g;
        let k = ((delta / g).rem_euclid(n) * s.rem_euclid(n)).rem_euclid(n);
        residue += modulus * k;
        modulus *= n;
    }
    Some((residue, modulus))
}

// ---------------------------------------------------------------------------
// Carried over: examples

// Carried over, without the command-line part: the GCD and the LCM with zero
// operands, and the Bézout coefficients of Euclid's back-substitution.
#[test]
fn ex1_gcd_lcm_and_bezout_coefficients() {
    let mut context = c();
    assert_eq!(number::gcd(&z(-54), &z(24), &mut context).unwrap(), z(6));
    assert_eq!(number::lcm(&z(-21), &z(6), &mut context).unwrap(), z(42));
    assert_eq!(number::gcd(&z(0), &z(0), &mut context).unwrap(), z(0));
    assert_eq!(number::lcm(&z(0), &z(5), &mut context).unwrap(), z(0));
    let bezout = number::extended_gcd(&z(240), &z(46), &mut context).unwrap();
    assert_eq!(
        (bezout.gcd(), bezout.left(), bezout.right()),
        (&z(2), &z(-9), &z(47))
    );
    // Back-substituting Euclid's steps: 47*46 - 9*240 = 2162 - 2160 = 2.
    assert_eq!(47 * 46 - 9 * 240, 2);
    assert_eq!(
        number::extended_gcd(&z(0), &z(0), &mut context)
            .unwrap()
            .to_string(),
        "gcd: 0; left: 0; right: 0"
    );
}

// Carried over: negative exponents, the empty power, the modulus one, a
// missing inverse as a value, and the domain errors of the integer
// functions.
#[test]
fn ex2_modular_powers_and_inverses() {
    let mut context = c();
    // 3*4 = 12 = 1 (mod 11), so 3^-2 = 4^2 = 16 = 5 (mod 11).
    assert_eq!(
        number::modular_power(&z(3), &z(-2), &z(11), &mut context).unwrap(),
        z(5)
    );
    // 3*5 = 15 = 1 (mod 7).
    assert_eq!(
        number::modular_inverse(&z(3), &z(7), &mut context).unwrap(),
        ModularInverse::Inverse(z(5))
    );
    // gcd(6, 9) = 3, so no inverse exists; this is a result, not an error.
    assert_eq!(
        number::modular_inverse(&z(6), &z(9), &mut context).unwrap(),
        ModularInverse::NonUnit(z(3))
    );
    // Residues lie in [0, m); exponent zero is the identity, also for 0^0.
    assert_eq!(
        number::modular_power(&z(-1), &z(1), &z(7), &mut context).unwrap(),
        z(6)
    );
    assert_eq!(
        number::modular_power(&z(0), &z(0), &z(7), &mut context).unwrap(),
        z(1)
    );
    // Modulo one, the identity and the inverse are zero.
    assert_eq!(
        number::modular_power(&z(5), &z(0), &z(1), &mut context).unwrap(),
        z(0)
    );
    assert_eq!(
        number::modular_inverse(&z(5), &z(1), &mut context).unwrap(),
        ModularInverse::Inverse(z(0))
    );
    for result in [
        number::modular_power(&z(6), &z(-1), &z(9), &mut context),
        number::modular_power(&z(2), &z(3), &z(0), &mut context),
    ] {
        assert_fault(&result.unwrap_err(), FaultKind::OutsideDomain);
    }
}

// Carried over: moduli need not be coprime, an inconsistent system is a
// value, the empty system is 0 mod 1, and a congruence reduces its residue.
#[test]
fn ex3_chinese_remaindering_accepts_non_coprime_moduli() {
    let mut context = c();
    // gcd(6, 9) = 3 divides 8 - 2, and 8 = 2 (mod 6), 8 = 8 (mod 9).
    let inputs = [
        congruence(2, 6, &mut context),
        congruence(8, 9, &mut context),
    ];
    let result = number::crt(&inputs, &mut context).unwrap();
    match &result {
        CrtResult::Solution(solution) => {
            assert_eq!((solution.residue(), solution.modulus()), (&z(8), &z(18)));
        }
        other => panic!("{other:?}"),
    }
    assert_eq!(result.to_string(), "8 mod 18");
    // x = 1 (mod 4) is odd, while x = 2 (mod 6) is even.
    let inputs = [
        congruence(1, 4, &mut context),
        congruence(2, 6, &mut context),
    ];
    let result = number::crt(&inputs, &mut context).unwrap();
    assert_eq!(result, CrtResult::Inconsistent);
    assert_eq!(result.to_string(), "inconsistent");
    assert_eq!(
        number::crt(&[], &mut context).unwrap().to_string(),
        "0 mod 1"
    );
    assert_eq!(congruence(-3, 5, &mut context).to_string(), "2 mod 5");
    assert_fault(
        &Congruence::new(&z(1), &z(0), &mut context).unwrap_err(),
        FaultKind::OutsideDomain,
    );
}

// ---------------------------------------------------------------------------
// Carried over: properties and boundaries

// Carried over without its case under an 8-bit limit, which
// `a_modular_power_takes_one_path_under_every_bit_limit` replaces: inverses
// and powers of every residue of every modulus up to 24 against an
// exhaustive search, and the domain errors by their kind.
#[test]
fn modular_operations_match_exhaustive_residues() {
    for m in 1_i64..=24 {
        for a in -24..=24 {
            let expected = match (0..m).find(|v| (a * v).rem_euclid(m) == 1 % m) {
                Some(inverse) => ModularInverse::Inverse(z(inverse)),
                None => ModularInverse::NonUnit(z(small_gcd(a.rem_euclid(m), m))),
            };
            assert_eq!(
                number::modular_inverse(&z(a), &z(m), &mut c()).unwrap(),
                expected,
                "{a} mod {m}"
            );
            let mut power = 1 % m;
            for e in 0..12 {
                assert_eq!(
                    number::modular_power(&z(a), &z(e), &z(m), &mut c()).unwrap(),
                    z(power)
                );
                power = (power * a).rem_euclid(m);
            }
            if let ModularInverse::Inverse(inverse) = expected {
                let inverse = wide_value(&inverse);
                assert_eq!(
                    wide_value(&number::modular_power(&z(a), &z(-2), &z(m), &mut c()).unwrap()),
                    inverse * inverse % i128::from(m)
                );
            }
        }
    }
    assert_fault(
        &number::modular_power(&z(6), &z(-1), &z(9), &mut c()).unwrap_err(),
        FaultKind::OutsideDomain,
    );
    for m in [0, -5] {
        assert_fault(
            &number::modular_inverse(&z(2), &z(m), &mut c()).unwrap_err(),
            FaultKind::OutsideDomain,
        );
        assert_fault(
            &number::modular_power(&z(2), &z(3), &z(m), &mut c()).unwrap_err(),
            FaultKind::OutsideDomain,
        );
    }
}

// Carried over: every system of two congruences with moduli up to 10 and a
// few residues, duplicates and inconsistent pairs among them, against an
// exhaustive search, and the empty system.
#[test]
fn crt_general_moduli_empty_duplicates_and_inconsistency() {
    match number::crt(&[], &mut c()).unwrap() {
        CrtResult::Solution(empty) => assert_eq!(empty.to_string(), "0 mod 1"),
        other => panic!("{other:?}"),
    }
    for m in 1..=10 {
        for n in 1..=10 {
            for a in [0, 2, 5, -3] {
                for d in [0, 1, 4, -2] {
                    let inputs = [congruence(a, m, &mut c()), congruence(d, n, &mut c())];
                    let result = number::crt(&inputs, &mut c()).unwrap();
                    let period = m / small_gcd(m, n) * n;
                    let expected = (0..period).find(|x| (x - a) % m == 0 && (x - d) % n == 0);
                    match result {
                        CrtResult::Solution(solution) => {
                            assert_eq!(Some(solution.residue().clone()), expected.map(z));
                            assert_eq!(solution.modulus(), &z(period));
                        }
                        CrtResult::Inconsistent => assert_eq!(expected, None),
                        other => panic!("{other:?}"),
                    }
                }
            }
        }
    }
}

// Mixed, carried over with the integer kernel as its carrier: a
// representative modular power returns its value with exactly the work it
// needs and fails one unit below; the residues and moduli of a congruence
// built under other limits are checked against the receiving limits; a
// cancelled request and a passed deadline end the power; and the storage of
// a result is admitted against `max_nodes`.
#[test]
fn request_budget_receiving_limits_preflight_and_cancellation() {
    let modulus = two_to_plus(127, -1);
    let workload =
        |context: &mut Context| number::modular_power(&z(3), &z(65537), &modulus, context);
    let mut full = c();
    let expected = workload(&mut full).unwrap();
    assert_eq!(
        expected.to_string(),
        "4569278088761131322242499456678237192"
    );
    let work = full.work_used();
    let mut exact = context(Limits::new().with_max_work(work));
    assert_eq!(workload(&mut exact).unwrap(), expected);
    let mut short = context(Limits::new().with_max_work(work - 1));
    assert_limit(&workload(&mut short).unwrap_err(), LimitField::Work);

    let wide_congruence = Congruence::new(&z(1), &two_to_plus(200, 0), &mut c()).unwrap();
    let mut receiving = context(Limits::new().with_max_integer_bits(100));
    assert_bits(
        &number::crt(&[wide_congruence], &mut receiving).unwrap_err(),
        201,
    );
    assert_eq!(receiving.work_used(), 0);

    let error = workload(&mut cancelled(Limits::new())).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Cancelled);
    let error = workload(&mut expired(Limits::new())).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::DeadlineExceeded);

    let mut no_storage = context(Limits::new().with_max_nodes(0));
    let error = number::modular_inverse(&z(0), &z(1), &mut no_storage).unwrap_err();
    assert_limit(&error, LimitField::Nodes);
    assert_eq!(error.exceeded().unwrap().scope(), Some(LimitScope::Value));
}

// ---------------------------------------------------------------------------
// One path for modular products

// The bound of every product of two residues modulo 251 is 16 bits. Under
// the default limits and under exactly 16 bits the power is computed on the
// same path with the same work; 15 and 8 bits reject it before any charge,
// although each operand has only 8 bits.
#[test]
fn a_modular_power_takes_one_path_under_every_bit_limit() {
    let power = |limits: Limits| {
        let mut context = context(limits);
        let result = number::modular_power(&z(250), &z(231), &z(251), &mut context);
        (result, context.work_used())
    };
    let (result, work) = power(Limits::new());
    assert_eq!(result.unwrap(), z(250));
    let (result, bounded) = power(Limits::new().with_max_integer_bits(16));
    assert_eq!(result.unwrap(), z(250));
    assert_eq!(bounded, work);
    for bits in [15, 8] {
        let (result, used) = power(Limits::new().with_max_integer_bits(bits));
        assert_bits(&result.unwrap_err(), 16);
        assert_eq!(used, 0);
    }
}

// ---------------------------------------------------------------------------
// Properties against machine-integer models

// 1,000 pairs below 2^62 in absolute value: the GCD is nonnegative, divides
// both operands and is the GCD of the model, and its coefficients satisfy
// the Bézout identity and are those of the model.
#[test]
fn bezout_identity_holds_for_seeded_operands() {
    let mut random = SplitMix64(0x5EED_0000_0300_0001);
    let mut context = c();
    for case in 0..1_000 {
        let (a, b) = random.pair(case);
        let bezout = number::extended_gcd(&z(a), &z(b), &mut context).unwrap();
        let gcd = number::gcd(&z(a), &z(b), &mut context).unwrap();
        assert_eq!(&gcd, bezout.gcd(), "{a}, {b}");
        let (g, s, t) = (
            wide_value(bezout.gcd()),
            wide_value(bezout.left()),
            wide_value(bezout.right()),
        );
        let (a, b) = (i128::from(a), i128::from(b));
        assert!(g >= 0, "{a}, {b}");
        if g != 0 {
            assert_eq!((a % g, b % g), (0, 0), "{a}, {b}");
        }
        assert_eq!(s * a + t * b, g, "{a}, {b}");
        assert_eq!((g, s, t), bezout_model(a, b), "{a}, {b}");
    }
}

// 1,000 pairs as above: the LCM is nonnegative, its product with the GCD is
// the absolute value of the product of the operands, and it is the LCM of
// the model.
#[test]
fn lcm_times_gcd_is_the_absolute_product() {
    let mut random = SplitMix64(0x5EED_0000_0300_0002);
    let mut context = c();
    for case in 0..1_000 {
        let (a, b) = random.pair(case);
        let l = wide_value(&number::lcm(&z(a), &z(b), &mut context).unwrap());
        let g = wide_value(&number::gcd(&z(a), &z(b), &mut context).unwrap());
        let (a, b) = (i128::from(a), i128::from(b));
        assert!(l >= 0, "{a}, {b}");
        assert_eq!(l * g, (a * b).abs(), "{a}, {b}");
        let model = if a == 0 || b == 0 {
            0
        } else {
            (a / bezout_model(a, b).0 * b).abs()
        };
        assert_eq!(l, model, "{a}, {b}");
    }
}

// 1,000 systems of one to four congruences, with moduli in 1..2^20, half of
// them below 65, and residues in -2^20..=2^20: a solution satisfies every
// congruence, lies in [0, l) for the LCM l of the moduli, has the modulus l
// and is the solution of the model; a system that the model finds
// inconsistent is inconsistent.
#[test]
fn crt_solutions_satisfy_every_congruence_and_are_unique_modulo_the_lcm() {
    let mut random = SplitMix64(0x5EED_0000_0300_0003);
    let mut context = c();
    let mut outcomes = [0_usize; 2];
    for _ in 0..1_000 {
        let count = random.between(1, 4);
        let system: Vec<(i64, i64)> = (0..count)
            .map(|_| {
                let modulus = if random.below(2) == 0 {
                    random.between(1, 64)
                } else {
                    random.between(1, (1 << 20) - 1)
                };
                (random.between(-(1 << 20), 1 << 20), modulus)
            })
            .collect();
        let inputs: Vec<Congruence> = system
            .iter()
            .map(|&(r, m)| congruence(r, m, &mut context))
            .collect();
        let wide_system: Vec<(i128, i128)> = system
            .iter()
            .map(|&(r, m)| (i128::from(r), i128::from(m)))
            .collect();
        let lcm = wide_system
            .iter()
            .fold(1_i128, |l, &(_, m)| l / bezout_model(l, m).0 * m);
        match number::crt(&inputs, &mut context).unwrap() {
            CrtResult::Solution(solution) => {
                let (r, m) = (
                    wide_value(solution.residue()),
                    wide_value(solution.modulus()),
                );
                assert_eq!(m, lcm, "{system:?}");
                assert!((0..m).contains(&r), "{system:?}");
                for &(ri, mi) in &wide_system {
                    assert_eq!((r - ri).rem_euclid(mi), 0, "{system:?}");
                }
                assert_eq!(Some((r, m)), crt_model(&wide_system), "{system:?}");
                outcomes[0] += 1;
            }
            CrtResult::Inconsistent => {
                assert_eq!(crt_model(&wide_system), None, "{system:?}");
                outcomes[1] += 1;
            }
            other => panic!("{other:?}"),
        }
    }
    assert!(outcomes[0] > 0 && outcomes[1] > 0, "{outcomes:?}");
}

// ---------------------------------------------------------------------------
// Bounds, charges and the domain

/// $-x$, built with the operations of `Rational`.
fn minus(x: &Integer) -> Integer {
    q(x).negate(&mut wide()).unwrap().numerator().clone()
}

/// Runs `operation` under exactly `bound` bits, where it must return its
/// value after a charge of `charge` units, and under `bound - 1` bits, where
/// it must fail with `max_integer_bits` and the amount `bound` before any
/// charge.
fn at_the_bound<T>(
    bound: u64,
    charge: u64,
    operation: impl Fn(&mut Context) -> kalyx::Result<T>,
) -> T {
    let mut exact = context(Limits::new().with_max_integer_bits(bound));
    let value = operation(&mut exact).ok().unwrap();
    assert_eq!(exact.work_used(), charge, "{bound} bits");
    let mut below = context(Limits::new().with_max_integer_bits(bound - 1));
    assert_bits(&operation(&mut below).err().unwrap(), bound);
    assert_eq!(below.work_used(), 0, "{bound} bits");
    value
}

/// Checks that $(q, r)$ is the Euclidean division of $a$ by $b$:
/// $a = q b + r$ and $0 \le r \lt \lvert b \rvert$, computed with the
/// operations of `Rational`.
fn assert_euclidean(a: &Integer, b: &Integer, quotient: &Integer, remainder: &Integer) {
    let context = &mut wide();
    let recomposed = q(quotient)
        .multiply(&q(b), context)
        .unwrap()
        .add(&q(remainder), context)
        .unwrap();
    assert_eq!(recomposed, q(a), "{a} / {b}");
    assert!(!remainder.is_negative(), "{a} / {b}");
    let magnitude = if b.is_negative() { minus(b) } else { b.clone() };
    assert_eq!(
        q(remainder).compare(&q(&magnitude), context).unwrap(),
        std::cmp::Ordering::Less,
        "{a} / {b}"
    );
}

// The operations of `Integer` with one-word and multi-word operands: each
// returns its value, checked with the operations of `Rational`, under exactly
// its bound and fails one bit below with `max_integer_bits` before any
// charge; sums, differences, negations and absolute values charge one unit,
// products and divisions $W(a) W(b)$. The Euclidean division of every
// dividend in -20..=20 by every divisor in ±1..±7 is that of `i64`, and a
// zero divisor fails before the bound and the charge.
#[test]
fn integer_operations_check_bits_before_charging() {
    let large = (two_to_plus(200, -1), minus(&two_to_plus(65, 3)));
    assert_eq!((large.0.bits(), large.1.bits()), (200, 66));
    assert_eq!(words(&large.0) * words(&large.1), 8);
    for (a, b) in [(z(5), z(-7)), large] {
        let (la, lb) = (a.bits(), b.bits());
        let words_ab = words(&a) * words(&b);
        let wide = &mut wide();

        let sum = at_the_bound(la.max(lb) + 1, 1, |c| a.add(&b, c));
        assert_eq!(q(&sum), q(&a).add(&q(&b), wide).unwrap());
        let difference = at_the_bound(la.max(lb) + 1, 1, |c| a.subtract(&b, c));
        assert_eq!(q(&difference), q(&a).subtract(&q(&b), wide).unwrap());
        let product = at_the_bound(la + lb, words_ab, |c| a.multiply(&b, c));
        assert_eq!(q(&product), q(&a).multiply(&q(&b), wide).unwrap());
        let negation = at_the_bound(la, 1, |c| a.negate(c));
        assert_eq!(q(&negation), q(&a).negate(wide).unwrap());
        let absolute = at_the_bound(lb, 1, |c| b.absolute(c));
        assert_eq!(q(&absolute), q(&b).negate(wide).unwrap());

        let division = at_the_bound(la.max(lb), words_ab, |c| a.divide_with_remainder(&b, c));
        assert_euclidean(&a, &b, division.quotient(), division.remainder());
        let exact = at_the_bound(product.bits().max(lb), words(&product) * words(&b), |c| {
            product.exact_quotient(&b, c)
        });
        assert_eq!(exact, ExactQuotient::Quotient(a.clone()));
        let inexact = at_the_bound(la.max(lb), words_ab, |c| a.exact_quotient(&b, c));
        assert_eq!(inexact, ExactQuotient::NotDivisible);
    }

    for a in -20_i64..=20 {
        for b in (-7_i64..=7).filter(|&b| b != 0) {
            let division = z(a).divide_with_remainder(&z(b), &mut c()).unwrap();
            assert_eq!(
                (division.quotient(), division.remainder()),
                (&z(a.div_euclid(b)), &z(a.rem_euclid(b))),
                "{a} / {b}"
            );
        }
    }

    let mut nothing = context(Limits::new().with_max_integer_bits(0).with_max_work(0));
    for a in [z(0), z(5), two_to_plus(200, -1)] {
        assert_fault(
            &a.divide_with_remainder(&z(0), &mut nothing).unwrap_err(),
            FaultKind::DivisionByZero,
        );
        assert_fault(
            &a.exact_quotient(&z(0), &mut nothing).unwrap_err(),
            FaultKind::DivisionByZero,
        );
    }
    assert_eq!(nothing.work_used(), 0);
}

// A modulus that is not positive is `OutsideDomain` before every check and
// charge, even with no bits and no work; a negative power of a residue that
// is not a unit is `OutsideDomain` after the charges of its inverse. Both
// are faults of the input.
#[test]
fn non_positive_moduli_and_negative_powers_of_non_units_are_outside_the_domain() {
    for m in [0, -5] {
        let mut nothing = context(Limits::new().with_max_integer_bits(0).with_max_work(0));
        let errors = [
            number::modular_inverse(&z(2), &z(m), &mut nothing).unwrap_err(),
            number::modular_power(&z(2), &z(3), &z(m), &mut nothing).unwrap_err(),
            Congruence::new(&z(2), &z(m), &mut nothing).unwrap_err(),
        ];
        for error in &errors {
            assert_fault(error, FaultKind::OutsideDomain);
            assert_eq!(error.kind().class(), ErrorClass::Input);
        }
        assert_eq!(nothing.work_used(), 0);
    }
    for base in [6, 0] {
        let mut inverse = c();
        assert_eq!(
            number::modular_inverse(&z(base), &z(9), &mut inverse).unwrap(),
            ModularInverse::NonUnit(z(if base == 0 { 9 } else { 3 }))
        );
        let mut power = c();
        let error = number::modular_power(&z(base), &z(-1), &z(9), &mut power).unwrap_err();
        assert_fault(&error, FaultKind::OutsideDomain);
        assert_eq!(error.kind().class(), ErrorClass::Input);
        assert!(power.work_used() > 0);
        assert_eq!(power.work_used(), inverse.work_used());
    }
}

// ---------------------------------------------------------------------------
// Storage

/// Runs `operation` with exactly `cost` of nodes and bytes, where it must
/// return its value, and with one byte and one node less, where it must fail
/// with that limit at the scope `Value`.
fn admitted_exactly<T>(cost: Storage, operation: impl Fn(&mut Context) -> kalyx::Result<T>) {
    let limits = Limits::new()
        .with_max_nodes(cost.nodes)
        .with_max_storage_bytes(cost.bytes);
    assert!(operation(&mut context(limits)).is_ok(), "{cost:?}");
    for (fewer, field) in [
        (
            limits.with_max_storage_bytes(cost.bytes - 1),
            LimitField::StorageBytes,
        ),
        (limits.with_max_nodes(cost.nodes - 1), LimitField::Nodes),
    ] {
        let error = operation(&mut context(fewer)).err().unwrap();
        assert_limit(&error, field);
        assert_eq!(error.exceeded().unwrap().scope(), Some(LimitScope::Value));
    }
}

// The storage costs of the results of the kernel, by the formulas of the
// architecture: an integer z costs one node and |z| + 4 bytes, as z/1 does,
// a result of several integers the sum of their costs, and an outcome
// without an integer one node and 4 bytes. Each result is admitted with
// exactly its cost and rejected with one byte or one node less.
#[test]
fn integer_results_are_measured_by_their_bits() {
    assert_eq!(z(-12).storage(), Storage::new(1, 8));
    assert_eq!(z(0).storage(), Storage::new(1, 4));
    assert_eq!(z(-12).storage(), q(&z(-12)).storage());
    admitted_exactly(Storage::new(1, 8), |c| z(-12).absolute(c).map(|_| ()));

    // -7 = (-4) * 2 + 1: 3 and 1 bits.
    let division = |c: &mut Context| z(-7).divide_with_remainder(&z(2), c);
    assert_eq!(division(&mut c()).unwrap().storage(), Storage::new(2, 12));
    admitted_exactly(Storage::new(2, 12), division);

    // (2, -9, 47): 2, 4 and 6 bits.
    let bezout = |c: &mut Context| number::extended_gcd(&z(240), &z(46), c);
    assert_eq!(bezout(&mut c()).unwrap().storage(), Storage::new(3, 24));
    admitted_exactly(Storage::new(3, 24), bezout);

    // 2 mod 5: 2 and 3 bits.
    let reduced = |c: &mut Context| Congruence::new(&z(-3), &z(5), c);
    assert_eq!(reduced(&mut c()).unwrap().storage(), Storage::new(2, 13));
    admitted_exactly(Storage::new(2, 13), reduced);

    let inverse = |c: &mut Context| number::modular_inverse(&z(3), &z(7), c);
    assert_eq!(inverse(&mut c()).unwrap(), ModularInverse::Inverse(z(5)));
    assert_eq!(inverse(&mut c()).unwrap().storage(), Storage::new(1, 7));
    admitted_exactly(Storage::new(1, 7), inverse);
    let non_unit = |c: &mut Context| number::modular_inverse(&z(6), &z(9), c);
    assert_eq!(non_unit(&mut c()).unwrap(), ModularInverse::NonUnit(z(3)));
    assert_eq!(non_unit(&mut c()).unwrap().storage(), Storage::new(1, 6));
    admitted_exactly(Storage::new(1, 6), non_unit);

    let inconsistent = |c: &mut Context| {
        let inputs = [congruence(1, 4, &mut wide()), congruence(2, 6, &mut wide())];
        number::crt(&inputs, c)
    };
    assert_eq!(inconsistent(&mut c()).unwrap(), CrtResult::Inconsistent);
    assert_eq!(CrtResult::Inconsistent.storage(), Storage::new(1, 4));
    admitted_exactly(Storage::new(1, 4), inconsistent);

    let not_divisible = |c: &mut Context| z(7).exact_quotient(&z(2), c);
    assert_eq!(
        not_divisible(&mut c()).unwrap(),
        ExactQuotient::NotDivisible
    );
    assert_eq!(ExactQuotient::NotDivisible.storage(), Storage::new(1, 4));
    admitted_exactly(Storage::new(1, 4), not_divisible);
    let quotient = |c: &mut Context| z(12).exact_quotient(&z(-4), c);
    assert_eq!(quotient(&mut c()).unwrap(), ExactQuotient::Quotient(z(-3)));
    assert_eq!(quotient(&mut c()).unwrap().storage(), Storage::new(1, 6));
    admitted_exactly(Storage::new(1, 6), quotient);
}

// ---------------------------------------------------------------------------
// The witnesses of the earlier specification

/// What a witness states of its call under its bounds.
#[derive(Clone, Copy)]
enum Stated {
    /// The call must return this outcome.
    Returns(&'static str),
    /// The call returns this outcome or fails with `ResourceLimit`.
    ReturnsOrLimit(&'static str),
    /// The call must stop at the first charge: when cancelled, when the
    /// deadline has passed, and when no work is left, then charging nothing.
    StopsAtTheFirstCharge,
    /// The call returns this outcome with the work it needs and with
    /// $10^9$ units, charging the same.
    ReturnsWithEveryBudget(&'static str),
}

/// A witness: a call, the bounds of bits, nodes and bytes under which it
/// is stated, what it states, and the bounds under which it must return no
/// value, each with the limit that it then exceeds.
struct Witness {
    name: &'static str,
    call: fn(&mut Context) -> kalyx::Result<String>,
    bits: u64,
    nodes: u64,
    bytes: u64,
    max_exponent: Option<u64>,
    stated: Stated,
    no_value: &'static [(u64, u64, u64, LimitField)],
}

/// The outcome of a call as text: the value, or the kind of the error.
fn outcome(result: kalyx::Result<String>) -> String {
    match result {
        Ok(value) => value,
        Err(error) => format!("{:?}", error.kind()),
    }
}

fn inverse_text(inverse: ModularInverse) -> String {
    match inverse {
        ModularInverse::Inverse(value) => format!("Inverse({value})"),
        ModularInverse::NonUnit(divisor) => format!("NonUnit({divisor})"),
        other => format!("{other:?}"),
    }
}

fn quotient_text(quotient: ExactQuotient) -> String {
    match quotient {
        ExactQuotient::Quotient(value) => value.to_string(),
        ExactQuotient::NotDivisible => String::from("NotDivisible"),
        other => format!("{other:?}"),
    }
}

/// The limits of `witness`: its bounds of bits, nodes and bytes, and the
/// other fields at their defaults.
fn stated_limits(witness: &Witness, bits: u64, nodes: u64, bytes: u64) -> Limits {
    let limits = Limits::new()
        .with_max_integer_bits(bits)
        .with_max_nodes(nodes)
        .with_max_storage_bytes(bytes);
    match witness.max_exponent {
        Some(exponent) => limits.with_max_exponent(exponent),
        None => limits,
    }
}

/// The bounds of `witness` with every other field at 0 and `max_work` at
/// `work`.
fn tight_limits(witness: &Witness, work: u64) -> Limits {
    Limits::new()
        .with_max_work(work)
        .with_max_input_bytes(0)
        .with_max_output_bytes(0)
        .with_max_depth(0)
        .with_max_nodes(witness.nodes)
        .with_max_storage_bytes(witness.bytes)
        .with_max_integer_bits(witness.bits)
        .with_max_exponent(0)
        .with_max_frames(0)
}

fn run(witness: &Witness, mut context: Context) -> (String, u64) {
    let outcome = outcome((witness.call)(&mut context));
    (outcome, context.work_used())
}

/// The witnesses of the integers and the residues of the earlier
/// implementation's specification, the theorems `*_must_return`,
/// `*_witness` and `*_limit_witness` of
/// `cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:verification/Casxi/Spec/IntegerRings.lean`
/// that have a counterpart in the integer kernel. Their bounds of bits and
/// nodes are those of the theorems; their bounds of bytes are recomputed by
/// the storage formulas of kalyx, where an integer $z$ costs
/// $\lvert z \rvert + 4$ bytes and the earlier formula
/// $\lceil \lvert z \rvert / 8 \rceil + 8$. An "any" bound of bits is 0.
const WITNESSES: [Witness; 24] = [
    Witness {
        name: "gcd_must_return: gcd(-12, 18)",
        call: |c| number::gcd(&z(-12), &z(18), c).map(|g| g.to_string()),
        bits: 5,
        nodes: 2,
        bytes: 17,
        max_exponent: None,
        stated: Stated::Returns("6"),
        // Only the returned value is admitted, so the operands of 2 nodes and
        // 17 bytes are not checked: the value 6 of (1, 7) needs a node and 7
        // bytes.
        no_value: &[
            (4, 2, 17, LimitField::IntegerBits),
            (5, 0, 17, LimitField::Nodes),
            (5, 2, 6, LimitField::StorageBytes),
        ],
    },
    Witness {
        name: "gcd_must_return: gcd(0, 0)",
        call: |c| number::gcd(&z(0), &z(0), c).map(|g| g.to_string()),
        bits: 0,
        nodes: 2,
        bytes: 8,
        max_exponent: None,
        stated: Stated::Returns("0"),
        no_value: &[],
    },
    Witness {
        name: "gcd_context_witness: gcd(-12, 18)",
        call: |c| number::gcd(&z(-12), &z(18), c).map(|g| g.to_string()),
        bits: 5,
        nodes: 2,
        bytes: 17,
        max_exponent: None,
        stated: Stated::StopsAtTheFirstCharge,
        no_value: &[],
    },
    Witness {
        name: "gcd_budget_witness: gcd(-12, 18)",
        call: |c| number::gcd(&z(-12), &z(18), c).map(|g| g.to_string()),
        bits: 5,
        nodes: 2,
        bytes: 17,
        max_exponent: None,
        stated: Stated::ReturnsWithEveryBudget("6"),
        no_value: &[],
    },
    Witness {
        name: "lcm_must_return: lcm(4, 6)",
        call: |c| number::lcm(&z(4), &z(6), c).map(|l| l.to_string()),
        bits: 5,
        nodes: 2,
        bytes: 14,
        max_exponent: None,
        stated: Stated::Returns("12"),
        no_value: &[(2, 2, 14, LimitField::IntegerBits)],
    },
    Witness {
        name: "intResidues_must_return: -3 mod 5",
        call: |c| Congruence::new(&z(-3), &z(5), c).map(|r| r.to_string()),
        bits: 3,
        nodes: 2,
        bytes: 14,
        max_exponent: None,
        stated: Stated::Returns("2 mod 5"),
        no_value: &[(2, 2, 14, LimitField::IntegerBits)],
    },
    Witness {
        name: "residueInverse_must_return: 3 modulo 7",
        call: |c| number::modular_inverse(&z(3), &z(7), c).map(inverse_text),
        bits: 5,
        nodes: 6,
        bytes: 42,
        max_exponent: None,
        stated: Stated::Returns("Inverse(5)"),
        no_value: &[(2, 6, 42, LimitField::IntegerBits)],
    },
    Witness {
        name: "residueInverse_nonUnit_must_return: 4 modulo 6",
        call: |c| number::modular_inverse(&z(4), &z(6), c).map(inverse_text),
        bits: 5,
        nodes: 6,
        bytes: 42,
        max_exponent: None,
        stated: Stated::Returns("NonUnit(2)"),
        no_value: &[],
    },
    Witness {
        name: "residueInverse_nonUnit_must_return: 6 modulo 9",
        call: |c| number::modular_inverse(&z(6), &z(9), c).map(inverse_text),
        bits: 6,
        nodes: 6,
        bytes: 48,
        max_exponent: None,
        stated: Stated::Returns("NonUnit(3)"),
        no_value: &[],
    },
    Witness {
        name: "residueInverse_zero_witness: 0 modulo 1",
        call: |c| number::modular_inverse(&z(0), &z(1), c).map(inverse_text),
        bits: 1,
        nodes: 2,
        bytes: 9,
        max_exponent: None,
        stated: Stated::Returns("Inverse(0)"),
        no_value: &[],
    },
    Witness {
        name: "residuePow_must_return: 3^-2 modulo 11",
        call: |c| number::modular_power(&z(3), &z(-2), &z(11), c).map(|p| p.to_string()),
        bits: 8,
        nodes: 6,
        bytes: 48,
        max_exponent: None,
        stated: Stated::Returns("5"),
        no_value: &[(7, 6, 48, LimitField::IntegerBits)],
    },
    Witness {
        name: "residuePow_must_return: 0^0 modulo 9",
        call: |c| number::modular_power(&z(0), &z(0), &z(9), c).map(|p| p.to_string()),
        bits: 4,
        nodes: 3,
        bytes: 16,
        max_exponent: None,
        stated: Stated::Returns("1"),
        no_value: &[],
    },
    Witness {
        name: "residuePow_exponent_bits_witness: 2^100000 modulo 1000003",
        call: |c| {
            number::modular_power(&z(2), &z(100_000), &z(1_000_003), c).map(|p| p.to_string())
        },
        bits: 40,
        nodes: 3,
        bytes: 51,
        max_exponent: Some(0),
        stated: Stated::Returns("491079"),
        no_value: &[],
    },
    Witness {
        name: "intOp_must_return: -12 + 18",
        call: |c| z(-12).add(&z(18), c).map(|v| v.to_string()),
        bits: 7,
        nodes: 2,
        bytes: 17,
        max_exponent: None,
        stated: Stated::Returns("6"),
        no_value: &[(4, 2, 17, LimitField::IntegerBits)],
    },
    Witness {
        name: "intOp_must_return: -12 - 18",
        call: |c| z(-12).subtract(&z(18), c).map(|v| v.to_string()),
        bits: 7,
        nodes: 2,
        bytes: 17,
        max_exponent: None,
        stated: Stated::Returns("-30"),
        no_value: &[(4, 2, 17, LimitField::IntegerBits)],
    },
    Witness {
        name: "intOp_must_return: -12 * 18",
        call: |c| z(-12).multiply(&z(18), c).map(|v| v.to_string()),
        bits: 9,
        nodes: 2,
        bytes: 17,
        max_exponent: None,
        stated: Stated::Returns("-216"),
        no_value: &[(4, 2, 17, LimitField::IntegerBits)],
    },
    Witness {
        name: "intNeg_must_return: -(-12)",
        call: |c| z(-12).negate(c).map(|v| v.to_string()),
        bits: 4,
        nodes: 1,
        bytes: 8,
        max_exponent: None,
        stated: Stated::Returns("12"),
        no_value: &[(3, 1, 8, LimitField::IntegerBits)],
    },
    Witness {
        name: "exactDiv_must_return: 12 / (-4)",
        call: |c| z(12).exact_quotient(&z(-4), c).map(quotient_text),
        bits: 5,
        nodes: 2,
        bytes: 15,
        max_exponent: None,
        stated: Stated::Returns("-3"),
        no_value: &[(3, 2, 15, LimitField::IntegerBits)],
    },
    Witness {
        name: "exactDiv_must_return: 7 / 2",
        call: |c| z(7).exact_quotient(&z(2), c).map(quotient_text),
        bits: 4,
        nodes: 2,
        bytes: 15,
        max_exponent: None,
        stated: Stated::Returns("NotDivisible"),
        no_value: &[],
    },
    Witness {
        name: "exactDiv_zero_witness: 5 / 0",
        call: |c| z(5).exact_quotient(&z(0), c).map(quotient_text),
        bits: 3,
        nodes: 2,
        bytes: 11,
        max_exponent: None,
        stated: Stated::Returns("Fault(DivisionByZero)"),
        no_value: &[],
    },
    Witness {
        name: "exactDiv_zero_witness: 0 / 0",
        call: |c| z(0).exact_quotient(&z(0), c).map(quotient_text),
        bits: 0,
        nodes: 2,
        bytes: 8,
        max_exponent: None,
        stated: Stated::Returns("Fault(DivisionByZero)"),
        no_value: &[],
    },
    Witness {
        name: "intOp_limit_witness: -12 + 18 at 6 bits",
        call: |c| z(-12).add(&z(18), c).map(|v| v.to_string()),
        bits: 6,
        nodes: 2,
        bytes: 17,
        max_exponent: None,
        stated: Stated::ReturnsOrLimit("6"),
        no_value: &[],
    },
    Witness {
        name: "exactDiv_limit_witness: 12 / (-4) at 4 bits",
        call: |c| z(12).exact_quotient(&z(-4), c).map(quotient_text),
        bits: 4,
        nodes: 2,
        bytes: 15,
        max_exponent: None,
        stated: Stated::ReturnsOrLimit("-3"),
        no_value: &[],
    },
    Witness {
        name: "residueInverse_limit_witness: 3 modulo 7 at 4 bits",
        call: |c| number::modular_inverse(&z(3), &z(7), c).map(inverse_text),
        bits: 4,
        nodes: 6,
        bytes: 42,
        max_exponent: None,
        stated: Stated::ReturnsOrLimit("Inverse(5)"),
        no_value: &[],
    },
];

// Each witness of the integers and residues runs at its stated bounds, with
// the other limits at their defaults and then at 0 with exactly the work it
// needs, and gives what it states; under the bounds below it returns no
// value.
#[test]
fn the_stated_bounds_of_the_integer_witnesses_admit_their_results() {
    for witness in &WITNESSES {
        let name = witness.name;
        let limits = stated_limits(witness, witness.bits, witness.nodes, witness.bytes);
        let (first, work) = run(witness, context(limits));
        match witness.stated {
            Stated::Returns(expected) | Stated::ReturnsWithEveryBudget(expected) => {
                assert_eq!(first, expected, "{name}");
            }
            Stated::ReturnsOrLimit(expected) => {
                assert!(
                    first == expected || first == "ResourceLimit",
                    "{name}: {first}"
                );
            }
            Stated::StopsAtTheFirstCharge => {
                let (stopped, used) = run(witness, cancelled(limits));
                assert_eq!((stopped.as_str(), used), ("Cancelled", 0), "{name}");
                let (stopped, _) = run(witness, expired(limits));
                assert_eq!(stopped, "DeadlineExceeded", "{name}");
                let (stopped, used) = run(witness, context(limits.with_max_work(0)));
                assert_eq!((stopped.as_str(), used), ("ResourceLimit", 0), "{name}");
                let mut none = context(limits.with_max_work(0));
                assert_limit(&(witness.call)(&mut none).unwrap_err(), LimitField::Work);
            }
        }
        if let Stated::ReturnsWithEveryBudget(expected) = witness.stated {
            for budget in [work, 1_000_000_000] {
                let (again, used) = run(witness, context(limits.with_max_work(budget)));
                assert_eq!((again.as_str(), used), (expected, work), "{name}: {budget}");
            }
        }
        let (tight, used) = run(witness, context(tight_limits(witness, work)));
        assert_eq!((tight, used), (first, work), "{name}");
        for &(bits, nodes, bytes, field) in witness.no_value {
            let mut below = context(stated_limits(witness, bits, nodes, bytes));
            let error = (witness.call)(&mut below).unwrap_err();
            assert_limit(&error, field);
        }
    }
}
