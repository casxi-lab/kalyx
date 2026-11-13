//! The crate-internal pair check of the coefficient fields, tested
//! directly, since no layer of the library calls it yet. The checks of the
//! coefficient traits are in `tests/coefficient.rs`.

use super::{CoefficientRing, PrimeField, require_same_parent};
use crate::context::CancelFlag;
use crate::number::Integer;
use crate::{Context, ErrorClass, ErrorKind, FaultKind, Limits};

// Negative: the element 2 of F_5 and the element 2 of F_7 have the same
// residue, so only their parents tell them apart, and the pair check of the
// two parents fails with `VariableMismatch`, a fault of the input, in either
// order, under a work limit of 0 and without a charge. Each parent with
// itself passes.
#[test]
fn elements_of_different_prime_fields_fail_with_variable_mismatch() {
    let built = &mut Context::new(Limits::new(), CancelFlag::new());
    let five = PrimeField::new(5, built).unwrap();
    let seven = PrimeField::new(7, built).unwrap();
    let two = Integer::from(2_i64);
    let in_five = five.from_integer(&two, built).unwrap();
    let in_seven = seven.from_integer(&two, built).unwrap();
    assert_eq!((in_five.value(), in_seven.value()), (2, 2));
    let context = &mut Context::new(Limits::new().with_max_work(0), CancelFlag::new());
    for (left, right) in [(&five, &seven), (&seven, &five)] {
        let error = require_same_parent(left, right, context).unwrap_err();
        assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::VariableMismatch));
        assert_eq!(error.kind().class(), ErrorClass::Input);
        assert_eq!(error.span(), None);
        assert!(error.exceeded().is_none());
    }
    require_same_parent(&five, &five, context).unwrap();
    require_same_parent(&seven, &seven, context).unwrap();
    assert_eq!(context.work_used(), 0);
}
