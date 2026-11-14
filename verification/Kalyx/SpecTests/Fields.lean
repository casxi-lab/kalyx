module

public meta import Kalyx.Spec.Fields.Integers
public meta import Kalyx.Spec.Fields.NumberField

/-!
# Replays of the vectors of the coefficient fields

The vectors of `vectors/cli_cases.tsv` whose answers only the element
operations of the coefficient fields decide, replayed through the
specification of `Kalyx.Spec.Fields` with `#guard`, each compared with the
expected value, the expected result state or the expected kind of error. A
command line reaches these operations through the parser and the command
entry, which the replays leave out: the operator precedence of `-2^2`, for
instance, is the parser's, and the replay computes the negation of the power.

The operations of the rationals and the integers are those of their
coefficient structures on fractions and integers. The number fields are
replayed on the minimal polynomial `x² + 1`, the list `[1, 0, 1]`, through the
operations that their coefficient field applies to the minimal polynomial of
its parent, since a parent carries the irreducibility of its polynomial, a
proof; the answers do not depend on the embedding.
-/

namespace Kalyx.SpecTests.Fields

open Kalyx.Spec.Fields

-- core/eval-adds-fractions: `1/3+1/6` is `1/2`.
#guard Rationals.field.add ⟨⟩ ⟨1, 3⟩ ⟨1, 6⟩ == .value ⟨1, 2⟩

-- core/eval-applies-power-before-negation: `-2^2` is `-4`, the negation of `2²`.
#guard ((ratPowOp 2 2).map Fraction.ofRat).bind (Rationals.field.negate ⟨⟩) == .value ⟨-4, 1⟩

-- core/eval-carries-past-u64: `18446744073709551615+1` is `18446744073709551616`,
-- as a rational and as an integer.
#guard Rationals.field.add ⟨⟩ ⟨18446744073709551615, 1⟩ ⟨1, 1⟩ ==
  .value ⟨18446744073709551616, 1⟩
#guard Integers.ring.add ⟨⟩ 18446744073709551615 1 == .value 18446744073709551616

-- core/eval-divides-negative-big-integers: `(-18446744073709551616)/(-1)` is
-- `18446744073709551616`.
#guard Rationals.field.divide ⟨⟩ ⟨-18446744073709551616, 1⟩ ⟨-1, 1⟩ ==
  .value ⟨18446744073709551616, 1⟩

-- core/eval-rejects-division-by-zero: `1/0` is `DivisionByZero`.
#guard Rationals.field.divide ⟨⟩ ⟨1, 1⟩ ⟨0, 1⟩ == .fault .divisionByZero

-- algebra/field-element-inverts-the-generator: in `field(x^2+1,1)`, `a^-1` is
-- `-a`.
#guard NumberField.inverse [1, 0, 1] (NumberField.generator [1, 0, 1]) ==
  .value (NumberField.negate [1, 0, 1] (NumberField.generator [1, 0, 1]))

-- algebra/field-element-rejects-division-by-zero: in `field(x^2+1,1)`, `a^2+1`
-- is zero and `1/(a^2+1)` is `DivisionByZero`.
#guard
  let m : List ℚ := [1, 0, 1]
  let a := NumberField.generator m
  let s := NumberField.add m (NumberField.multiply m a a) (NumberField.ofRat m 1)
  NumberField.zeroTest s == .zero && NumberField.divide m (NumberField.ofRat m 1) s == .fault .divisionByZero

end Kalyx.SpecTests.Fields
