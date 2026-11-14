module

public import Kalyx.Spec.Fields.Laws
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

/-!
# The rationals

The rationals are interpreted in `ℚ` (numbers contract, "Rationals" and
FLD-R01 to FLD-R04 and FLD-R12). The library stores a rational as a fraction
of an integer numerator and an integer denominator (`Fraction`); the canonical
fractions are those in lowest terms with a positive denominator
(`Fraction.Reduced`), and zero is `0/1`. `Rationals.field` is the
coefficient field of the zero-sized parent `Rationals` on fractions, and
`Rationals.model` its interpretation.

The operations on rational values come in two layers. The domain layer returns
the `Outcome` of an operation apart from the limits: a value, or
`DivisionByZero` for a zero divisor, the inverse of zero and a negative power
of zero (`ratDivOp`, `ratInvOp`, `ratPowOp` and `RatOp.exact`). The checked
layer states which outcomes an operation may have under the explicit limits
`maxIntegerBits` and `maxExponent`, in the order of kalyx: the domain tests,
then the bits. An integer power first compares its exponent with
`maxExponent` and reports `ResourceLimit` naming it when it is above, before
the zero test of its base. The bits are checked in the form that may report
(`SizeCheck.Admits`), against the estimates of the earlier implementation
(FLD-R12 and FLD-R03), which are never below the bounds of kalyx (numbers
contract, "Checks and charges"): above the estimate an operation may report
`ResourceLimit` naming `max_integer_bits`, and at or below it, since the
estimate bounds the bits of the result, it returns the value. The bits of a
rational are the larger bit length of its numerator and its denominator, at
least 1 (`ratBits`).
-/

@[expose] public section

namespace Kalyx.Spec.Fields

/-! ## Fractions -/

/-- The parent of the rationals, kalyx's zero-sized `Rationals`: it holds no
data, so there is one rational field. -/
structure Rationals where
  deriving DecidableEq, Repr

/-- A fraction as the library stores a rational: an integer numerator and an
integer denominator. The values of the library are the reduced fractions
(`Fraction.Reduced`); the others, such as `2/4` and `1/(-2)`, are
representatives that the specification can name. -/
structure Fraction where
  /-- The numerator. -/
  num : ℤ
  /-- The denominator. -/
  den : ℤ
  deriving DecidableEq, Repr

/-- The canonical form of a rational (FLD-R01): a positive denominator, and no
common factor of the numerator and the denominator, so that zero is `0/1`. -/
def Fraction.Reduced (f : Fraction) : Prop := 0 < f.den ∧ Int.gcd f.num f.den = 1

/-- The rational number that a fraction denotes. A fraction with the
denominator zero is not reduced and denotes no number; Lean's division by
zero makes it denote `0`. -/
def Fraction.interpret (f : Fraction) : ℚ := (f.num : ℚ) / (f.den : ℚ)

/-- The reduced fraction of a rational number: Mathlib's `ℚ` stores the
numerator and the positive denominator in lowest terms. -/
def Fraction.ofRat (q : ℚ) : Fraction := ⟨q.num, q.den⟩

/-- The reduction of a fraction with a nonzero denominator: the reduced
fraction of the number that it denotes, as `2/4` reduces to `1/2`. -/
def Fraction.reduce (f : Fraction) : Fraction := Fraction.ofRat f.interpret

/-! ## The domain layer -/

/-- Division: by zero it is undefined. -/
def ratDiv (a b : ℚ) : Option ℚ :=
  if b = 0 then none else some (a / b)

/-- Integer powers: `a ^ 0 = 1` for every `a`, including `0 ^ 0`; a negative
power of zero is undefined. -/
def ratPow (a : ℚ) (n : ℤ) : Option ℚ :=
  if a = 0 ∧ n < 0 then none else some (a ^ n)

/-- The zero test of a rational, which always decides. -/
def ratIsZero (a : ℚ) : ZeroTest Empty := ZeroTest.ofDecide (a = 0)

/-- Division in the domain layer: by zero it is `DivisionByZero`. -/
def ratDivOp (a b : ℚ) : Outcome ℚ := FieldError.lift .divisionByZero (ratDiv a b)

/-- Inversion in the domain layer: zero has no inverse (`DivisionByZero`). -/
def ratInvOp (a : ℚ) : Outcome ℚ :=
  if a = 0 then .fault .divisionByZero else .value a⁻¹

/-- Integer powers in the domain layer: a negative power of zero inverts zero
first and is `DivisionByZero`. -/
def ratPowOp (a : ℚ) (n : ℤ) : Outcome ℚ := FieldError.lift .divisionByZero (ratPow a n)

/-- The binary operations of the rationals. -/
inductive RatOp where
  /-- The sum. -/
  | add
  /-- The difference. -/
  | sub
  /-- The product. -/
  | mul
  /-- The quotient. -/
  | div
  deriving DecidableEq, Repr

/-- The outcome of a binary rational operation in the domain layer: sums,
differences and products are defined everywhere, and a quotient by zero is
`DivisionByZero`. -/
def RatOp.exact : RatOp → ℚ → ℚ → Outcome ℚ
  | .add, a, b => .value (a + b)
  | .sub, a, b => .value (a - b)
  | .mul, a, b => .value (a * b)
  | .div, a, b => ratDivOp a b

/-- The unary operations of the rationals whose bound is the bits of the
operand: negation and inversion. -/
inductive RatUnary where
  /-- The additive inverse. -/
  | neg
  /-- The multiplicative inverse. -/
  | inv
  deriving DecidableEq, Repr

/-- The outcome of a unary rational operation in the domain layer: the
negation is defined everywhere, and the inverse of zero is
`DivisionByZero`. -/
def RatUnary.exact : RatUnary → ℚ → Outcome ℚ
  | .neg, a => .value (-a)
  | .inv, a => ratInvOp a

/-! ## The rationals as a coefficient field -/

/-- The rationals as a coefficient field (numbers contract, "Rationals"): one
parent; `zero`, `one` and `fromInteger` are the fractions `0/1`, `1/1` and
`n/1`; the other operations are those of the rational values that the
fractions denote, returned as reduced fractions; the zero test always decides;
and `measure` is the storage cost of a rational, one node and
`|n| + |d| + 3` bytes for `n/d`, where `|x|` is the bit length of the absolute
value. -/
def Rationals.field : CoefficientField Rationals Fraction Empty where
  sameParent _ _ := true
  zero _ := ⟨0, 1⟩
  one _ := ⟨1, 1⟩
  fromInteger _ n := ⟨n, 1⟩
  negate _ a := (RatUnary.exact .neg a.interpret).map Fraction.ofRat
  add _ a b := (RatOp.exact .add a.interpret b.interpret).map Fraction.ofRat
  subtract _ a b := (RatOp.exact .sub a.interpret b.interpret).map Fraction.ofRat
  multiply _ a b := (RatOp.exact .mul a.interpret b.interpret).map Fraction.ofRat
  zeroTest _ a := .value (ratIsZero a.interpret)
  measure _ a := ⟨1, a.num.natAbs.size + a.den.natAbs.size + 3⟩
  inverse _ a := (RatUnary.exact .inv a.interpret).map Fraction.ofRat
  divide _ a b := (RatOp.exact .div a.interpret b.interpret).map Fraction.ofRat

/-- The interpretation of the rationals: a fraction denotes the rational
number `num / den`, and the reduced fractions are canonical. -/
def Rationals.model : Model Rationals Fraction (fun _ => ℚ) :=
  fun _ => ⟨Fraction.interpret, Fraction.Reduced⟩

/-! ## The checked layer -/

/-- The bits of a rational: the larger bit length (`Nat.size`) of its absolute
numerator and its denominator, at least 1 since the denominator is positive. -/
def ratBits (q : ℚ) : ℕ := max q.num.natAbs.size q.den.size

/-- A new element `q`, as `zero`, `one` and `fromInteger` build it, checked
against `maxIntegerBits`: the bits of the element are the amount, and the check
decides. -/
def checkBits (maxIntegerBits : ℕ) (q : ℚ) : Outcome ℚ :=
  checkLimit .integerBits maxIntegerBits (ratBits q) (.value q)

/-- The estimate of the bits of the result of a binary rational operation,
computed from its operands and checked before the result is computed. With
`n₁`, `d₁`, `n₂` and `d₂` the bit lengths of the absolute numerators and of the
denominators of the operands, it is
`max (max (n₁ + d₂) (n₂ + d₁) + 1) (d₁ + d₂)` for sums and differences,
`max (n₁ + n₂) (d₁ + d₂)` for products and `max (n₁ + d₂) (d₁ + n₂)` for
quotients. -/
def RatOp.estimate : RatOp → ℚ → ℚ → ℕ
  | .add, a, b | .sub, a, b =>
    max (max (a.num.natAbs.size + b.den.size) (b.num.natAbs.size + a.den.size) + 1)
      (a.den.size + b.den.size)
  | .mul, a, b => max (a.num.natAbs.size + b.num.natAbs.size) (a.den.size + b.den.size)
  | .div, a, b => max (a.num.natAbs.size + b.den.size) (a.den.size + b.num.natAbs.size)

/-- The bit checks of a binary rational operation under `maxIntegerBits`: its
estimate, and the bits of its result. -/
def RatOp.check (op : RatOp) (maxIntegerBits : ℕ) (a b : ℚ) : SizeCheck ℚ :=
  SizeCheck.ofBound maxIntegerBits (op.estimate a b) ratBits

/-- The outcomes that a binary rational operation admits under
`maxIntegerBits` (FLD-R12): the zero divisor of a quotient is
`DivisionByZero` under every limit; a value is returned when it is within the
limit; and `ResourceLimit` naming `max_integer_bits` may be reported in place
of a value where the estimate is above the limit. -/
def RatOp.Admits (op : RatOp) (maxIntegerBits : ℕ) (a b : ℚ) : Outcome ℚ → Prop :=
  (op.check maxIntegerBits a b).Admits .integerBits (op.exact a b)

/-- The outcomes that the negation and the inversion of `a` admit under
`maxIntegerBits`: their bound is the bits of `a`, and the inverse of zero is
`DivisionByZero` under every limit. -/
def RatUnary.Admits (op : RatUnary) (maxIntegerBits : ℕ) (a : ℚ) : Outcome ℚ → Prop :=
  (SizeCheck.ofBound maxIntegerBits (ratBits a) ratBits).Admits .integerBits (op.exact a)

/-- The estimate of the bits of the integer power `a ^ n` (FLD-R03): `|n|`
times the bits of `a`, plus one. It bounds the power. -/
def ratPowEstimate (a : ℚ) (n : ℤ) : ℕ := n.natAbs * ratBits a + 1

/-- The bit checks of the integer power `a ^ n` under `maxIntegerBits`: the
larger of its estimate and the bits of the base, so that the base is checked
for the exponent zero too, and the bits of the result. -/
def ratPowCheck (maxIntegerBits : ℕ) (a : ℚ) (n : ℤ) : SizeCheck ℚ :=
  SizeCheck.ofBound maxIntegerBits (max (ratPowEstimate a n) (ratBits a)) ratBits

/-- The outcomes that the integer power `a ^ n` admits under `maxExponent` and
`maxIntegerBits` (FLD-R03): an exponent whose absolute value is above
`maxExponent` is `ResourceLimit` naming `max_exponent`, before the zero test of
the base; then a negative power of zero is `DivisionByZero`; then the bits are
checked by `ratPowCheck`. -/
def ratPowAdmits (maxExponent maxIntegerBits : ℕ) (a : ℚ) (n : ℤ) : Outcome ℚ → Prop :=
  (ratPowCheck maxIntegerBits a n).Admits .integerBits
    (checkLimit .exponent maxExponent n.natAbs (ratPowOp a n))

end Kalyx.Spec.Fields

end
