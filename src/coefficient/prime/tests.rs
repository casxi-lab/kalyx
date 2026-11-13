//! The four kernels of the prime fields, tested directly: on every triple
//! of residues modulo the primes from 11 to 31 they satisfy the field axioms
//! and agree with 64-bit arithmetic written here, and every residue modulo
//! 65521 has its inverse. The checks of the coefficient traits, which call
//! the kernels, are in `tests/coefficient.rs`.

use super::PrimeField;
use crate::context::CancelFlag;
use crate::{Context, Limits};

/// The field of `p`, built by its constructor.
fn field(p: u32) -> PrimeField {
    let context = &mut Context::new(Limits::new(), CancelFlag::new());
    PrimeField::new(p, context).unwrap()
}

/// The kernels on every triple $(a, b, c)$ of residues modulo `p`: the
/// sum, the difference and the product agree with 64-bit arithmetic;
/// the sum and the product are commutative and associative, the product
/// distributes over the sum, 0 and 1 are their neutral elements, and
/// $(a - b) + b = a$; and every nonzero $a$ has $a \cdot a^{-1} = 1$.
fn every_triple_satisfies_the_field_axioms(p: u32) {
    let f = field(p);
    let wide = u64::from(p);
    for a in 0..p {
        let (x, y) = (u64::from(a), wide);
        assert_eq!(f.add(a, 0), a, "{a} + 0 modulo {p}");
        assert_eq!(f.mul(a, 1), a, "{a} 1 modulo {p}");
        assert_eq!(f.mul(a, 0), 0, "{a} 0 modulo {p}");
        assert_eq!(f.add(a, f.sub(0, a)), 0, "{a} + (-{a}) modulo {p}");
        assert_eq!(u64::from(f.sub(0, a)), (y - x) % y, "-{a} modulo {p}");
        if a != 0 {
            assert_eq!(f.mul(a, f.inverse(a)), 1, "{a} / {a} modulo {p}");
        }
        for b in 0..p {
            let z = u64::from(b);
            assert_eq!(u64::from(f.add(a, b)), (x + z) % y, "{a} + {b} modulo {p}");
            assert_eq!(
                u64::from(f.sub(a, b)),
                (x + y - z) % y,
                "{a} - {b} modulo {p}"
            );
            assert_eq!(u64::from(f.mul(a, b)), x * z % y, "{a} {b} modulo {p}");
            assert_eq!(f.add(a, b), f.add(b, a), "{a} + {b} = {b} + {a} modulo {p}");
            assert_eq!(f.mul(a, b), f.mul(b, a), "{a} {b} = {b} {a} modulo {p}");
            assert_eq!(f.add(f.sub(a, b), b), a, "({a} - {b}) + {b} modulo {p}");
            for c in 0..p {
                assert_eq!(
                    f.add(f.add(a, b), c),
                    f.add(a, f.add(b, c)),
                    "({a} + {b}) + {c} modulo {p}"
                );
                assert_eq!(
                    f.mul(f.mul(a, b), c),
                    f.mul(a, f.mul(b, c)),
                    "({a} {b}) {c} modulo {p}"
                );
                assert_eq!(
                    f.mul(a, f.add(b, c)),
                    f.add(f.mul(a, b), f.mul(a, c)),
                    "{a} ({b} + {c}) modulo {p}"
                );
            }
        }
    }
}

#[test]
fn every_residue_triple_below_32_and_every_inverse_modulo_65521_is_exact() {
    for p in [11, 13, 17, 19, 23, 29, 31] {
        every_triple_satisfies_the_field_axioms(p);
    }
    let p = 65_521;
    let f = field(p);
    for a in 1..p {
        let inverse = f.inverse(a);
        assert!(inverse < p, "1 / {a} modulo {p} is a residue");
        assert_eq!(
            u64::from(a) * u64::from(inverse) % u64::from(p),
            1,
            "1 / {a} modulo {p}"
        );
    }
}
