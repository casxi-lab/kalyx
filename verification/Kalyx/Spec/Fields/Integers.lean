module

public import Kalyx.Spec.Fields.Rationals

/-!
# The integers

The integers as a coefficient ring are interpreted in `ℤ` (numbers contract,
FLD-R14, with FLD-R04 and FLD-R12). Every integer, of any size, is its own
canonical form, so the elements are integers and the interpretation is the
identity. The integers have no parent value: their parent `Integers` holds no
data. `Integers.ring` is the ring with the result-state subtrait of exact
division, and `Integers.model` its interpretation. The units of the integers
are `1` and `-1`, the units of `ℤ`.

The operations come in the two layers of the rationals. The domain layer
returns the `Outcome` of an operation apart from the limits: sums,
differences, products and negations are defined everywhere (`IntOp.exact`,
`intNegOp`), and exact division (`exactDivOp`) returns the quotient when the
divisor divides the dividend, the result state `inexact`, which is neither an
error nor a rounded quotient, when it does not, and `DivisionByZero` for a
zero divisor, `0 / 0` included. The checked layer states which outcomes an
operation may have under the explicit limit `maxIntegerBits`, in the order of
kalyx: the test of a zero divisor, then the bits. The bits are checked in the
form that may report (`SizeCheck.Admits`), against the bounds of the integer
kernel (numbers contract, "The integer kernel"), which are computed from the
operands and bound the bits of the result: `max |a| |b| + 1` for sums and
differences, `|a| + |b|` for products, `|a|` for negations and `max |a| |b|`
for exact division, where `|x|` is the bit length of the absolute value
(`intBits`), and zero has no bits. Above its bound an operation may report
`ResourceLimit` naming `max_integer_bits`; at or below it, it returns its
outcome. A zero divisor is `DivisionByZero` under every limit.

`measure` of an integer `z` is one node and `|z| + 4` bytes, the cost of the
rational `z/1`.
-/

@[expose] public section

namespace Kalyx.Spec.Fields

/-! ## Integers -/

/-- The parent of the integers, a zero-sized type: it holds no data, so there
is one ring of integers. -/
structure Integers where
  deriving DecidableEq, Repr

/-- The bits of an integer, as `Integer::bits` counts them: the bit length of
its absolute value. Zero has no bits, while the rational zero has one, the bit
of its denominator (`ratBits`). -/
def intBits (a : ℤ) : ℕ := a.natAbs.size

/-! ## The domain layer -/

/-- The zero test of an integer, which always decides. -/
def intIsZero (a : ℤ) : ZeroTest Empty := ZeroTest.ofDecide (a = 0)

/-- The sums, differences and products of integers. -/
inductive IntOp where
  /-- The sum. -/
  | add
  /-- The difference. -/
  | sub
  /-- The product. -/
  | mul
  deriving DecidableEq, Repr

/-- The value of a ring operation on integers, defined everywhere. -/
def IntOp.value : IntOp → ℤ → ℤ → ℤ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

/-- A ring operation on integers in the domain layer: never a fault. -/
def IntOp.exact (op : IntOp) (a b : ℤ) : Outcome ℤ := .value (op.value a b)

/-- The negation of an integer in the domain layer: never a fault. -/
def intNegOp (a : ℤ) : Outcome ℤ := .value (-a)

/-- Exact division where it is defined: undefined for a zero divisor, `0 / 0`
included; otherwise the quotient when the divisor divides the dividend, and the
result state `inexact` when it does not. -/
def exactDiv (a b : ℤ) : Option (ExactQuotient ℤ) :=
  if b = 0 then none else if b ∣ a then some (.exact (a / b)) else some .inexact

/-- Exact division in the domain layer: a zero divisor is `DivisionByZero`. -/
def exactDivOp (a b : ℤ) : Outcome (ExactQuotient ℤ) :=
  FieldError.lift .divisionByZero (exactDiv a b)

/-! ## The integers as a coefficient ring -/

/-- The integers as a coefficient ring with exact division (numbers contract,
FLD-R14): one parent; `zero`, `one` and `fromInteger` are `0`, `1` and `n`;
the ring operations and exact division are those of the domain layer; the
zero test always decides; and `measure` is the storage cost of an integer `z`,
one node and `|z| + 4` bytes. -/
def Integers.ring : ExactDivisionRing Integers ℤ Empty where
  sameParent _ _ := true
  zero _ := 0
  one _ := 1
  fromInteger _ n := n
  negate _ a := intNegOp a
  add _ a b := IntOp.exact .add a b
  subtract _ a b := IntOp.exact .sub a b
  multiply _ a b := IntOp.exact .mul a b
  zeroTest _ a := .value (intIsZero a)
  measure _ a := ⟨1, intBits a + 4⟩
  exactDivide _ a b := exactDivOp a b

/-- The interpretation of the integers: an integer denotes itself, and every
integer is canonical. -/
def Integers.model : Model Integers ℤ (fun _ => ℤ) :=
  fun _ => ⟨id, fun _ => True⟩

/-! ## The checked layer -/

/-- The bound of the integer kernel on the bits of the result of a ring
operation, computed from its operands and checked before the result is
computed: with `b₁` and `b₂` the bits of the operands, `max b₁ b₂ + 1` for a
sum or a difference and `b₁ + b₂` for a product. -/
def IntOp.estimate : IntOp → ℤ → ℤ → ℕ
  | .add, a, b | .sub, a, b => max (intBits a) (intBits b) + 1
  | .mul, a, b => intBits a + intBits b

/-- The bit checks of a ring operation on integers under `maxIntegerBits`: its
bound, and the bits of its result. -/
def IntOp.check (op : IntOp) (maxIntegerBits : ℕ) (a b : ℤ) : SizeCheck ℤ :=
  SizeCheck.ofBound maxIntegerBits (op.estimate a b) intBits

/-- The outcomes that a ring operation on integers admits under
`maxIntegerBits` (FLD-R12): a value within the limit, and `ResourceLimit`
naming `max_integer_bits` in place of a value where the bound is above the
limit. -/
def IntOp.Admits (op : IntOp) (maxIntegerBits : ℕ) (a b : ℤ) : Outcome ℤ → Prop :=
  (op.check maxIntegerBits a b).Admits .integerBits (op.exact a b)

/-- The outcomes that the negation of `a` admits under `maxIntegerBits`: its
bound is the bits of `a`. -/
def intNegAdmits (maxIntegerBits : ℕ) (a : ℤ) : Outcome ℤ → Prop :=
  (SizeCheck.ofBound maxIntegerBits (intBits a) intBits).Admits .integerBits (intNegOp a)

/-- The bits of the outcome of an exact division: those of the quotient; the
result state `inexact` holds no integer. -/
def quotientBits : ExactQuotient ℤ → ℕ
  | .exact q => intBits q
  | .inexact => 0

/-- The bound of the integer kernel on the bits of an exact division: the
larger bits of the operands. -/
def exactDivEstimate (a b : ℤ) : ℕ := max (intBits a) (intBits b)

/-- The outcomes that the exact division of `a` by `b` admits under
`maxIntegerBits` (FLD-R12): a zero divisor is `DivisionByZero` under every
limit; otherwise the quotient or `inexact`, and `ResourceLimit` naming
`max_integer_bits` in place of them where the bound is above the limit. -/
def exactDivAdmits (maxIntegerBits : ℕ) (a b : ℤ) : Outcome (ExactQuotient ℤ) → Prop :=
  (SizeCheck.ofBound maxIntegerBits (exactDivEstimate a b) quotientBits).Admits .integerBits
    (exactDivOp a b)

end Kalyx.Spec.Fields

end
