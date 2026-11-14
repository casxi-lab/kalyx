module

public import Kalyx.Spec.Fields.PrimeField
public import Mathlib.Data.PNat.Defs
public import Mathlib.Data.ZMod.Basic

/-!
# The residue rings

The residue ring `ℤ/n` of a modulus `n ≥ 1` is interpreted in `ZMod n`
(numbers contract, FLD-R15, with FLD-R04). Its parent `ResidueRing` holds the
modulus, a positive natural number, and two parents are the same exactly when
their moduli are equal. Building a residue ring from an integer modulus
rejects a modulus `m ≤ 0` (`ResidueRing.new`, whose `Construction.rejected`
the library reports as `OutsideDomain`). `ℤ/1` is the zero ring, in which
`0 = 1`. An element is a natural number, the residue that the library stores;
the canonical residues modulo `n` are the least nonnegative ones, those below
`n`, and `ResidueRing.model` interprets a residue as its class in `ZMod n`.
The residue ring modulo a prime `p` and the prime field `𝔽_p` are different
parents over the same ring `ZMod p`.

The operations come in two layers. The domain layer computes in `ZMod n` and
returns the `Outcome` of an operation:

* sums, differences and products are defined everywhere (`ResidueOp.exact`),
  and the zero test always decides (`residueIsZero`);
* a residue is a unit exactly when it is prime to the modulus. The inverse
  (`residueInverseOp`) gives a unit its inverse and a nonzero residue that is
  not a unit the result state `nonUnit d`, where `d = gcd(a, n)` is a proper
  factor of the modulus, which is neither a fault nor zero. For a modulus
  above one the inverse of zero is `DivisionByZero`, as in the prime fields;
  in `ℤ/1`, zero is a unit and its own inverse;
* division and negative powers have the outcomes of the inverse of the
  divisor and of the base (`residueDivOp`, `residuePowOp`), so that for a
  modulus above one a division by zero and a negative power of zero are
  `DivisionByZero`; `a ^ 0 = 1`, `0 ^ 0` included.

`ResidueRing.ring` is the coefficient ring of the stored residues, with the
result-state subtrait of the inverse of a unit. Every method that takes
residues, `measure` apart, first tests that each is below the modulus and
fails with `OutsideDomain` otherwise, since such a residue cannot belong to
the ring; it then computes in `ZMod n` and returns the least nonnegative
residue of the result. Its `measure` is a parameter: a total function of the
parent and the residue, whose formula the implementation fixes.

A residue tagged with its parent (`ResidueTagged`) is what a layer that stores
parents with their elements combines: residues of different parents are a
`VariableMismatch`, decided before the operation and so before a zero divisor
(`ResidueTagged.lift`). The checks of the limits of the residue rings are not
stated here.
-/

@[expose] public section

namespace Kalyx.Spec.Fields

/-! ## Parents -/

/-- The parent of the residue ring `ℤ/n`: its modulus `n ≥ 1`. Two parents are
the same exactly when their moduli are equal. -/
structure ResidueRing where
  /-- The modulus. -/
  modulus : ℕ+
  deriving DecidableEq, Repr

/-- The residue ring of an integer modulus `m`: the ring of `m` for `m > 0`,
built from `Nat.toPNat'`, which is the identity on positive numbers, and
`rejected` for `m ≤ 0`, which the library reports as `OutsideDomain`, as the
integer functions do. -/
def ResidueRing.new (m : ℤ) : Construction ResidueRing :=
  if 0 < m then .built ⟨m.toNat.toPNat'⟩ else .rejected

/-- The interpretation of the residue rings: a residue denotes its class in
`ZMod n`, and the residues below the modulus, the least nonnegative ones, are
canonical. -/
def ResidueRing.model : Model ResidueRing ℕ (fun R => ZMod R.modulus) :=
  fun R => ⟨fun r => (r : ZMod R.modulus), fun r => r < R.modulus⟩

/-! ## The domain layer -/

/-- The zero test of a residue, which always decides. -/
def residueIsZero (n : ℕ) (a : ZMod n) : ZeroTest Empty := ZeroTest.ofDecide (a = 0)

/-- The sums, differences and products of residues. -/
inductive ResidueOp where
  /-- The sum. -/
  | add
  /-- The difference. -/
  | sub
  /-- The product. -/
  | mul
  deriving DecidableEq, Repr

/-- The value of a ring operation on residues, defined everywhere. -/
def ResidueOp.value {n : ℕ} : ResidueOp → ZMod n → ZMod n → ZMod n
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

/-- A ring operation on residues in the domain layer: never a fault. -/
def ResidueOp.exact {n : ℕ} (op : ResidueOp) (a b : ZMod n) : Outcome (ZMod n) :=
  .value (op.value a b)

/-- The rule for zero in a residue ring with a modulus above one: the inverse
of zero has no value and no result state, so that the domain layer reports
`DivisionByZero` for it, for a division by zero and for a negative power of
zero, as the prime fields do. -/
def residueZeroInverse (n : ℕ) : Option (UnitInverse (ZMod n)) := none

/-- The inverse where it is defined: the inverse of a unit, the result state
`nonUnit` of a nonzero residue that is not a unit with the factor `gcd(a, n)`
of the modulus, and for zero in a ring with a modulus above one the rule
`residueZeroInverse`. Mathlib's `a⁻¹` is used only for a unit, where it is the
inverse. -/
def residueInverse (n : ℕ) (a : ZMod n) : Option (UnitInverse (ZMod n)) :=
  if a = 0 ∧ 1 < n then residueZeroInverse n
  else if Nat.gcd a.val n = 1 then some (.unit a⁻¹) else some (.nonUnit (Nat.gcd a.val n))

/-- The inverse in the domain layer: an undefined inverse is
`DivisionByZero`. -/
def residueInverseOp (n : ℕ) (a : ZMod n) : Outcome (UnitInverse (ZMod n)) :=
  FieldError.lift .divisionByZero (residueInverse n a)

/-- The outcome of a division or a power in `ZMod n`: the value, or the result
state that the divisor, or the base of a negative power, is not a unit, with
the factor of the modulus that shows it. -/
inductive ResidueOutcome (n : ℕ) where
  /-- The value of the division or the power. -/
  | value (v : ZMod n)
  /-- The divisor, or the base, is not a unit; `factor` shows it. -/
  | nonUnit (factor : ℕ)
  deriving DecidableEq, Repr

/-- The outcome of a division or a power from the outcome of an inverse: the
value `f u` from the inverse `u` of a unit, and the result state of a residue
that is not a unit with its factor. -/
def UnitInverse.outcome {n : ℕ} (f : ZMod n → ZMod n) :
    UnitInverse (ZMod n) → ResidueOutcome n
  | .unit u => .value (f u)
  | .nonUnit d => .nonUnit d

/-- Division where it is defined: `a / b` is `a b⁻¹`, with the outcomes of
`b⁻¹`. -/
def residueDiv (n : ℕ) (a b : ZMod n) : Option (ResidueOutcome n) :=
  (residueInverse n b).map (UnitInverse.outcome (a * ·))

/-- Division in the domain layer: an undefined quotient is
`DivisionByZero`. -/
def residueDivOp (n : ℕ) (a b : ZMod n) : Outcome (ResidueOutcome n) :=
  FieldError.lift .divisionByZero (residueDiv n a b)

/-- Integer powers where they are defined: `a ^ e` for `e ≥ 0`, with
`a ^ 0 = 1` for every `a`, `0 ^ 0` included; and `(a⁻¹) ^ |e|` for `e < 0`,
with the outcomes of `a⁻¹`. -/
def residuePow (n : ℕ) (a : ZMod n) (e : ℤ) : Option (ResidueOutcome n) :=
  if 0 ≤ e then some (.value (a ^ e.toNat))
  else (residueInverse n a).map (UnitInverse.outcome (· ^ e.natAbs))

/-- Integer powers in the domain layer: an undefined power is
`DivisionByZero`. -/
def residuePowOp (n : ℕ) (a : ZMod n) (e : ℤ) : Outcome (ResidueOutcome n) :=
  FieldError.lift .divisionByZero (residuePow n a e)

/-! ## The residue rings as coefficient rings -/

/-- The outcome of the inverse of a unit with `f` applied to the inverse; the
result state of a residue that is not a unit is kept. -/
def UnitInverse.map {α β : Type} (f : α → β) : UnitInverse α → UnitInverse β
  | .unit u => .unit (f u)
  | .nonUnit d => .nonUnit d

/-- A residue that a method of the ring `R` takes: `next` of its class in
`ZMod n` when it is below the modulus, and `OutsideDomain` otherwise, since a
residue at or above the modulus cannot belong to `R`. -/
def ResidueRing.residue {α : Type} (R : ResidueRing) (a : ℕ)
    (next : ZMod R.modulus → Outcome α) : Outcome α :=
  if a < R.modulus then next a else .fault .outsideDomain

/-- A ring operation of the ring `R` on two stored residues: each is tested
against the modulus, and the least nonnegative residue of the result in
`ZMod n` is returned. -/
def ResidueRing.op (R : ResidueRing) (op : ResidueOp) (a b : ℕ) : Outcome ℕ :=
  R.residue a fun x => R.residue b fun y => (op.exact x y).map ZMod.val

/-- The residue rings as coefficient rings with the inverse of a unit
(numbers contract, FLD-R15), with the storage cost `μ` as their `measure`:
`zero`, `one` and `fromInteger` are the least nonnegative residues of `0`, `1`
and `n`, so that `one` is `0` in `ℤ/1`; the other methods test their residues
against the modulus and compute in `ZMod n`; the zero test always decides. -/
def ResidueRing.ring (μ : ResidueRing → ℕ → Storage) :
    UnitInverseRing ResidueRing ℕ Empty where
  sameParent R S := decide (R = S)
  zero _ := 0
  one R := (1 : ZMod R.modulus).val
  fromInteger R k := (k : ZMod R.modulus).val
  negate R a := R.residue a fun x => .value (-x).val
  add R a b := R.op .add a b
  subtract R a b := R.op .sub a b
  multiply R a b := R.op .mul a b
  zeroTest R a := R.residue a fun x => .value (residueIsZero R.modulus x)
  measure := μ
  unitInverse R a :=
    R.residue a fun x => (residueInverseOp R.modulus x).map (UnitInverse.map ZMod.val)

/-! ## Residues of different parents -/

/-- A residue tagged with its parent, as a layer that stores parents with
their elements passes residues: the parent and the class of the residue in
`ZMod n`. -/
abbrev ResidueTagged := Σ R : ResidueRing, ZMod R.modulus

/-- A residue of a parent read in an equal parent. -/
def ResidueTagged.transfer {R S : ResidueRing} (h : R = S) (a : ZMod R.modulus) :
    ZMod S.modulus :=
  h ▸ a

/-- A binary operation on tagged residues. Residues of different parents are a
`VariableMismatch`, decided before the operation, and hence before a zero
divisor is considered; residues of the same parent are combined in their ring,
and the result is tagged with that parent. -/
def ResidueTagged.lift {β : ResidueRing → Type}
    (op : ∀ R : ResidueRing, ZMod R.modulus → ZMod R.modulus → Outcome (β R))
    (x y : ResidueTagged) : Outcome (Σ R : ResidueRing, β R) :=
  if h : x.1 = y.1 then
    (op x.1 x.2 (ResidueTagged.transfer h.symm y.2)).map fun r => ⟨x.1, r⟩
  else .fault .variableMismatch

/-- A ring operation on tagged residues. -/
def ResidueTagged.ringOp (op : ResidueOp) :
    ResidueTagged → ResidueTagged → Outcome ResidueTagged :=
  ResidueTagged.lift fun _ a b => op.exact a b

/-- Division of tagged residues. -/
def ResidueTagged.div :
    ResidueTagged → ResidueTagged → Outcome (Σ R : ResidueRing, ResidueOutcome R.modulus) :=
  ResidueTagged.lift fun R a b => residueDivOp R.modulus a b

end Kalyx.Spec.Fields

end
