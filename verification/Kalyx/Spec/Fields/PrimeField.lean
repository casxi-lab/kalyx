module

public import Kalyx.Spec.Fields.Integers
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum.Prime

/-!
# The prime fields

The prime field `𝔽_p` of a prime `p` below `2 ^ 32` (numbers contract, "Prime
fields", and FLD-R01, FLD-R02, FLD-R04 and FLD-R12) is interpreted in
`ZMod p`. The parent `PrimeField` holds the modulus together with what its
constructor `PrimeField.new` established for it: the modulus is prime and fits
a machine word (`WordModulus`). The constructor rejects exactly the moduli that
are not prime (`Construction.rejected`, which the library reports as
`OutsideDomain`). An element is a `PrimeResidue`, a natural number; the
canonical residues of the field of `p` are the least nonnegative ones, those
below `p`, and `PrimeField.model` interprets a residue as its class in
`ZMod p`.

The methods of `PrimeField.field` wrap the operations on `ZMod p`. Every method
that takes residues, `measure` apart, first tests that each is below the
modulus and fails with `OutsideDomain` otherwise, since such a residue can
belong only to another field; it then computes in `ZMod p` and returns the
least nonnegative residue of the result. The inverse of zero and every
quotient by zero are `DivisionByZero` (`primeInverseOp`, `primeDivOp`), as in
every field; the earlier implementation made them an internal invariant
failure of the prime fields.

The checked layer (`PrimeMethod.Admits`) states which outcomes a method that
builds a residue may have under the explicit limit `maxIntegerBits`, in the
order of kalyx: the residue tests, then the zero test of `inverse` and
`divide`, then the bits. A fault of the domain layer is therefore never
replaced by `ResourceLimit`, under any limit. The bit bound of a new residue is
the bit length of the modulus, whatever the residue, and that of
`fromInteger n` the larger of the bit lengths of `n` and of the modulus
(numbers contract, the table of the methods); the bound is checked in the form
that may report (`SizeCheck.Admits`). The checks and the charges of the
constructor, and the charges, cancellation and deadlines of the methods, are
not part of this specification.

Under a word modulus the residues fit a `u32`, and the product of two of them
is below `2 ^ 64`, so that it fits the `u64` intermediate of a multiplication.
The operations of this specification are those of `ZMod p` and do not depend
on the bound.
-/

@[expose] public section

namespace Kalyx.Spec.Fields

/-! ## Construction -/

/-- The outcome of building a parent from defining data: the parent, or the
value `rejected` of invalid defining data, which the library reports as
`OutsideDomain`. -/
inductive Construction (α : Type) where
  /-- The defining data are valid, and this is the parent built from them. -/
  | built (parent : α)
  /-- The defining data are invalid. -/
  | rejected
  deriving DecidableEq, Repr

/-- The modulus of a machine-word prime field fits the word and the `u64`
intermediates of the operations: `p < 2 ^ 32`. -/
def WordModulus (p : ℕ) : Prop := p < 2 ^ 32

/-- The parent of a prime field, kalyx's `PrimeField`: the modulus `p`, with
the two facts that the constructor `PrimeField.new`, the only way to build a
parent, established for it. Two parents are the same exactly when their moduli
are equal. -/
structure PrimeField where
  /-- The modulus `p`. -/
  modulus : ℕ
  /-- The modulus is prime. -/
  prime : modulus.Prime
  /-- The modulus fits a machine word. -/
  word : WordModulus modulus
  deriving DecidableEq, Repr

/-- The constructor `PrimeField::new`: the field of a prime modulus below
`2 ^ 32`, and `rejected`, which the library reports as `OutsideDomain`, for
every other modulus. The library decides primality by a strong probable-prime
test that is exact for every `u32`; the specification states the decision. A
modulus of `2 ^ 32` or more is not a `u32` and never reaches the library; the
specification rejects it, so that every parent has a word modulus. -/
def PrimeField.new (p : ℕ) : Construction PrimeField :=
  if h : p.Prime ∧ p < 2 ^ 32 then .built ⟨p, h.1, h.2⟩ else .rejected

/-- An element of a prime field as the library stores it, kalyx's
`PrimeResidue`: a natural number, which the methods of a field take as a
residue modulo its modulus. The canonical residues of the field of `p` are
those below `p`; the others, such as `7` for `𝔽_7`, are representatives that
the specification can name, and the methods reject them with
`OutsideDomain`. -/
structure PrimeResidue where
  /-- The stored residue. -/
  value : ℕ
  deriving DecidableEq, Repr

/-! ## Residue classes

The operations on the classes of `ZMod p`, where the inverse and the quotient
may be undefined, and their domain layer. -/

/-- Inversion: the inverse of a nonzero residue; zero has none. -/
def primeInverse (p : ℕ) (a : ZMod p) : Option (ZMod p) :=
  if a = 0 then none else some a⁻¹

/-- Division of residues: by zero it is undefined, otherwise the product with
the inverse of the divisor. -/
def primeDiv (p : ℕ) (a b : ZMod p) : Option (ZMod p) :=
  (primeInverse p b).map (a * ·)

/-- Inversion in the domain layer: zero has no inverse (`DivisionByZero`). -/
def primeInverseOp (p : ℕ) (a : ZMod p) : Outcome (ZMod p) :=
  FieldError.lift .divisionByZero (primeInverse p a)

/-- Division in the domain layer: zero is no divisor (`DivisionByZero`). -/
def primeDivOp (p : ℕ) (a b : ZMod p) : Outcome (ZMod p) :=
  FieldError.lift .divisionByZero (primeDiv p a b)

/-- The zero test of a residue class, which always decides. -/
def primeIsZero (p : ℕ) (a : ZMod p) : ZeroTest Empty := ZeroTest.ofDecide (a = 0)

/-! ## The prime fields as coefficient fields -/

/-- The class in `ZMod p` of a residue. -/
def PrimeField.toZMod (F : PrimeField) (a : PrimeResidue) : ZMod F.modulus := a.value

/-- The least nonnegative residue of a class, `ZMod.val`. -/
def PrimeField.ofZMod (F : PrimeField) (x : ZMod F.modulus) : PrimeResidue := ⟨x.val⟩

/-- The residue test of every method that takes residues, `measure` apart:
`next`, the outcome of the rest of the method, when `a` is below the modulus,
and otherwise `OutsideDomain`, before anything of `next` is considered. -/
def PrimeField.requireResidue {α : Type} (F : PrimeField) (a : PrimeResidue)
    (next : Outcome α) : Outcome α :=
  if a.value < F.modulus then next else .fault .outsideDomain

/-- A method of one residue: the residue test, then `op` on its class, whose
result is returned as its least nonnegative residue. -/
def PrimeField.unary (F : PrimeField) (op : ZMod F.modulus → Outcome (ZMod F.modulus))
    (a : PrimeResidue) : Outcome PrimeResidue :=
  F.requireResidue a ((op (F.toZMod a)).map F.ofZMod)

/-- A method of two residues: the residue tests of both, then `op` on their
classes, whose result is returned as its least nonnegative residue. -/
def PrimeField.binary (F : PrimeField)
    (op : ZMod F.modulus → ZMod F.modulus → Outcome (ZMod F.modulus))
    (a b : PrimeResidue) : Outcome PrimeResidue :=
  F.requireResidue a (F.requireResidue b ((op (F.toZMod a) (F.toZMod b)).map F.ofZMod))

/-- The prime fields as coefficient fields (numbers contract, "Prime fields"):
two parents are the same when their moduli are equal; `zero` and `one` are the
residues `0` and `1`, and `fromInteger p n` is the Euclidean remainder of `n`
by `p`; the other methods test their residues and compute in `ZMod p`; the zero
test always decides; and `measure` is the storage cost of the integer `r`, one
node and `|r| + 4` bytes for the residue `r`, where `|r|` is its bit length. -/
def PrimeField.field : CoefficientField PrimeField PrimeResidue Empty where
  sameParent F G := decide (F.modulus = G.modulus)
  zero _ := ⟨0⟩
  one _ := ⟨1⟩
  fromInteger F n := ⟨(n % (F.modulus : ℤ)).toNat⟩
  negate F := F.unary fun x => .value (-x)
  add F := F.binary fun x y => .value (x + y)
  subtract F := F.binary fun x y => .value (x - y)
  multiply F := F.binary fun x y => .value (x * y)
  zeroTest F a := F.requireResidue a (.value (primeIsZero F.modulus (F.toZMod a)))
  measure _ a := ⟨1, a.value.size + 4⟩
  inverse F := F.unary (primeInverseOp F.modulus)
  divide F := F.binary (primeDivOp F.modulus)

/-- The interpretation of the prime fields: a residue denotes its class in
`ZMod p`, and the residues below `p` are canonical. -/
def PrimeField.model : Model PrimeField PrimeResidue (fun F => ZMod F.modulus) :=
  fun F => ⟨F.toZMod, fun a => a.value < F.modulus⟩

/-! ## The checked layer -/

/-- The bits of a residue: the bit length (`Nat.size`) of its value. -/
def PrimeResidue.bits (a : PrimeResidue) : ℕ := a.value.size

/-- The methods of a prime field that build a residue, with their operands. -/
inductive PrimeMethod where
  /-- `zero`. -/
  | zero
  /-- `one`. -/
  | one
  /-- `from_integer(n)`. -/
  | fromInteger (n : ℤ)
  /-- `negate(a)`. -/
  | negate (a : PrimeResidue)
  /-- `add(a, b)`. -/
  | add (a b : PrimeResidue)
  /-- `subtract(a, b)`. -/
  | subtract (a b : PrimeResidue)
  /-- `multiply(a, b)`. -/
  | multiply (a b : PrimeResidue)
  /-- `inverse(a)`. -/
  | inverse (a : PrimeResidue)
  /-- `divide(a, b)`. -/
  | divide (a b : PrimeResidue)
  deriving DecidableEq, Repr

/-- The outcome of a method of the field `F` in the domain layer, the method of
`PrimeField.field`. -/
def PrimeMethod.domain (F : PrimeField) : PrimeMethod → Outcome PrimeResidue
  | .zero => .value (PrimeField.field.zero F)
  | .one => .value (PrimeField.field.one F)
  | .fromInteger n => .value (PrimeField.field.fromInteger F n)
  | .negate a => PrimeField.field.negate F a
  | .add a b => PrimeField.field.add F a b
  | .subtract a b => PrimeField.field.subtract F a b
  | .multiply a b => PrimeField.field.multiply F a b
  | .inverse a => PrimeField.field.inverse F a
  | .divide a b => PrimeField.field.divide F a b

/-- The bit bound of a method of the field `F`, computed from the modulus and,
for `fromInteger n`, from `n`, before the result: the bit length of the
modulus, and for `fromInteger n` the larger of the bits of `n` (`intBits`) and
the bit length of the modulus. -/
def PrimeMethod.bound (F : PrimeField) : PrimeMethod → ℕ
  | .fromInteger n => max (intBits n) F.modulus.size
  | _ => F.modulus.size

/-- The outcomes that a method of the field `F` admits under `maxIntegerBits`
(FLD-R12): a residue at or above the modulus is `OutsideDomain`, and the
inverse of zero and a quotient by zero are `DivisionByZero`, under every limit;
a residue is returned when its bits are within the limit; and `ResourceLimit`
naming `max_integer_bits` may be reported in place of a residue where the bound
of the method is above the limit. -/
def PrimeMethod.Admits (maxIntegerBits : ℕ) (F : PrimeField) (m : PrimeMethod) :
    Outcome PrimeResidue → Prop :=
  (SizeCheck.ofBound maxIntegerBits (m.bound F) PrimeResidue.bits).Admits .integerBits
    (m.domain F)

end Kalyx.Spec.Fields

end
