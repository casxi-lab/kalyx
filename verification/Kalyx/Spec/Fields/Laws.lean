module

public import Kalyx.Spec.Fields.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Divisibility.Basic

/-!
# The coefficient-field trait and its laws

`CoefficientRing` and `CoefficientField` are the two traits of the numbers
contract ("The coefficient-field trait") as functions of a parent of type `P`
and elements of type `E`, with the reason `U` of an undecided zero test. Every
method takes the parent, as the Rust methods take `&self`, and elements do not
repeat their parent. The methods assume that their elements belong to the
parent; only a layer that stores a parent together with an element compares
parents, with the pair check `CoefficientRing.requireSameParent`. The rings
that are not fields have result-state subtraits for the divisions that may
fail: exact division (`ExactDivisionRing`) and the inverse of a unit
(`UnitInverseRing`).

The request context is not part of these definitions. Each method returns the
outcome of its domain layer: its value, or a fault such as `DivisionByZero`
or the `OutsideDomain` of an element that cannot belong to the parent. The
checks of the limits are stated with each structure. `measure` takes no
context and cannot fail.

The laws give the methods their meaning through an interpretation in Mathlib
(`Model`): for each parent `p`, a commutative ring `K p` and a canonical
representation of its elements by the elements `E` (`Canonical`). The
rationals are interpreted in `ℚ`, the integers in `ℤ`, the residue rings and
the prime fields in `ZMod n`, and the number fields in `AdjoinRoot m`. Every
law speaks of canonical elements only.

* `RingLaws`: canonical forms are unique, and the interpretation takes `zero`,
  `one`, `fromInteger`, `negate`, `add`, `subtract` and `multiply` to the
  operations of `K p`, each returning a canonical value. Since the
  interpretation is injective on canonical forms, the operations on them
  satisfy the axioms of a commutative ring with one, those of `K p`. That
  every element of `K p` has a canonical form is `Canonical.Complete` of
  `M p`.
* `FieldLaws`: the inverse of a nonzero element multiplies with it to one, a
  quotient multiplies with the divisor to the dividend, and zero has no
  inverse and is no divisor (`DivisionByZero`).
* `ExactDivisionLaws` and `UnitInverseLaws`: the result states of the rings
  that are not fields.
* `ZeroTestSound` and `ZeroTestExact`: a decided answer of the zero test is
  correct; an exact test always decides.
* `SameParentLaw`: two parents are the same exactly when their defining data
  are equal.

`measure` returns the storage cost of an element as a total function
`P → E → Storage`, which is the law of the contract: the cost depends only on
the parent and the element, the method reads no limits and it cannot fail.
The formula is each structure's own.
-/

@[expose] public section

namespace Kalyx.Spec.Fields

/-! ## The trait -/

/-- A storage cost, as kalyx's `Storage`: retained nodes and logical bytes. -/
structure Storage where
  /-- The retained nodes. -/
  nodes : ℕ
  /-- The retained logical bytes. -/
  bytes : ℕ
  deriving DecidableEq, Repr

/-- The methods of the trait `CoefficientRing` on the parents `P` and the
elements `E`, with the reason `U` of an undecided zero test. -/
structure CoefficientRing (P E U : Type) where
  /-- `same_parent`: whether two parents are the same structure. -/
  sameParent : P → P → Bool
  /-- `zero`: the zero of the parent. -/
  zero : P → E
  /-- `one`: the one of the parent. -/
  one : P → E
  /-- `from_integer`: the image of an integer, `n · 1`. -/
  fromInteger : P → ℤ → E
  /-- `negate`: the additive inverse. -/
  negate : P → E → Outcome E
  /-- `add`: the sum. -/
  add : P → E → E → Outcome E
  /-- `subtract`: the difference. -/
  subtract : P → E → E → Outcome E
  /-- `multiply`: the product. -/
  multiply : P → E → E → Outcome E
  /-- `zero_test`: whether the element is zero. -/
  zeroTest : P → E → Outcome (ZeroTest U)
  /-- `measure`: the storage cost of the element, a total function of the
  parent and the element, which reads no limits and cannot fail. -/
  measure : P → E → Storage

/-- The methods of the trait `CoefficientField`: those of `CoefficientRing`,
and the inverse and the quotient. -/
structure CoefficientField (P E U : Type) extends CoefficientRing P E U where
  /-- `inverse`: the multiplicative inverse; zero has none. -/
  inverse : P → E → Outcome E
  /-- `divide`: the quotient; zero is no divisor. -/
  divide : P → E → E → Outcome E

/-- The outcome of an exact division: the quotient, or the result state
`inexact` that the divisor does not divide the dividend, which is neither an
error nor a rounded quotient. -/
inductive ExactQuotient (E : Type) where
  /-- The divisor divides the dividend, with this quotient. -/
  | exact (quotient : E)
  /-- The divisor does not divide the dividend. -/
  | inexact
  deriving DecidableEq, Repr

/-- A coefficient ring with the result-state subtrait of exact division. -/
structure ExactDivisionRing (P E U : Type) extends CoefficientRing P E U where
  /-- Exact division: the quotient, `inexact`, or a fault for a zero divisor. -/
  exactDivide : P → E → E → Outcome (ExactQuotient E)

/-- The outcome of the inverse of a unit: the inverse, or the result state
that the element is not a unit, with a divisor that shows it. -/
inductive UnitInverse (E : Type) where
  /-- The element is a unit, with this inverse. -/
  | unit (inverse : E)
  /-- The element is not a unit; `divisor` shows it. -/
  | nonUnit (divisor : ℕ)
  deriving DecidableEq, Repr

/-- A coefficient ring with the result-state subtrait of the inverse of a
unit. -/
structure UnitInverseRing (P E U : Type) extends CoefficientRing P E U where
  /-- The inverse of a unit: the inverse, `nonUnit`, or a fault for zero. -/
  unitInverse : P → E → Outcome (UnitInverse E)

/-! ## The pair check -/

/-- The pair check `require_same_parent`, before a layer that stores parents
with their elements combines the elements of the parents `p` and `q`: `next`,
the outcome of the combination, when the parents are the same, and otherwise
`VariableMismatch`, before anything of `next` is considered, a zero divisor
included. -/
def CoefficientRing.requireSameParent {P E U α : Type} (R : CoefficientRing P E U) (p q : P)
    (next : Outcome α) : Outcome α :=
  if R.sameParent p q then next else .fault .variableMismatch

/-- A binary operation `op` of `R` on two elements stored with their parents:
the pair check, then `op` in the parent of the first pair, whose result is
stored with that parent. -/
def CoefficientRing.paired {P E U α : Type} (R : CoefficientRing P E U)
    (op : P → E → E → Outcome α) (x y : P × E) : Outcome (P × α) :=
  R.requireSameParent x.1 y.1 ((op x.1 x.2 y.2).map fun r => (x.1, r))

/-! ## Interpretations -/

/-- An interpretation of the elements `E` of the parents `P` in Mathlib: for
each parent `p`, the elements of the structure `K p` that the elements denote
and the canonical elements among them. -/
abbrev Model (P E : Type) (K : P → Type) : Type := (p : P) → Canonical E (K p)

/-- The outcome `o` is a canonical value of the parent `p` that denotes `x`. -/
def Model.Yields {P E : Type} {K : P → Type} (M : Model P E K) (p : P) (o : Outcome E)
    (x : K p) : Prop :=
  ∃ e, o = .value e ∧ (M p).canonical e ∧ (M p).interpret e = x

/-! ## Laws -/

/-- Parents are compared by their defining data: `sameParent` holds exactly
for equal parents. -/
def SameParentLaw {P E U : Type} (R : CoefficientRing P E U) : Prop :=
  ∀ p q, R.sameParent p q = true ↔ p = q

/-- The ring laws of `R` under the interpretation `M`: canonical forms are
unique, and on canonical elements the ring operations return canonical values
that denote the results of the operations of `K p`. -/
structure RingLaws {P E U : Type} {K : P → Type} [∀ p, CommRing (K p)]
    (R : CoefficientRing P E U) (M : Model P E K) : Prop where
  /-- The interpretation is injective on canonical elements. -/
  unique : ∀ p, (M p).Unique
  /-- `zero` is canonical and denotes `0`. -/
  zero : ∀ p, (M p).canonical (R.zero p) ∧ (M p).interpret (R.zero p) = 0
  /-- `one` is canonical and denotes `1`. -/
  one : ∀ p, (M p).canonical (R.one p) ∧ (M p).interpret (R.one p) = 1
  /-- `fromInteger p n` is canonical and denotes the image of `n`. -/
  fromInteger : ∀ p (n : ℤ),
    (M p).canonical (R.fromInteger p n) ∧ (M p).interpret (R.fromInteger p n) = n
  /-- `negate` denotes the additive inverse. -/
  negate : ∀ p a, (M p).canonical a → M.Yields p (R.negate p a) (-(M p).interpret a)
  /-- `add` denotes the sum. -/
  add : ∀ p a b, (M p).canonical a → (M p).canonical b →
    M.Yields p (R.add p a b) ((M p).interpret a + (M p).interpret b)
  /-- `subtract` denotes the difference. -/
  subtract : ∀ p a b, (M p).canonical a → (M p).canonical b →
    M.Yields p (R.subtract p a b) ((M p).interpret a - (M p).interpret b)
  /-- `multiply` denotes the product. -/
  multiply : ∀ p a b, (M p).canonical a → (M p).canonical b →
    M.Yields p (R.multiply p a b) ((M p).interpret a * (M p).interpret b)

/-- The field laws of `F` under `M`: on canonical elements, the inverse of a
nonzero element is a canonical value whose product with it denotes one, and a
quotient by a nonzero divisor is a canonical value whose product with the
divisor denotes the dividend; zero has no inverse and is no divisor, and both
are `DivisionByZero`. -/
structure FieldLaws {P E U : Type} {K : P → Type} [∀ p, CommRing (K p)]
    (F : CoefficientField P E U) (M : Model P E K) : Prop where
  /-- A nonzero element has an inverse. -/
  inverse : ∀ p a, (M p).canonical a → (M p).interpret a ≠ 0 →
    ∃ b, F.inverse p a = .value b ∧ (M p).canonical b ∧
      (M p).interpret a * (M p).interpret b = 1
  /-- Zero has no inverse. -/
  inverse_zero : ∀ p a, (M p).canonical a → (M p).interpret a = 0 →
    F.inverse p a = .fault .divisionByZero
  /-- A nonzero divisor has a quotient. -/
  divide : ∀ p a b, (M p).canonical a → (M p).canonical b → (M p).interpret b ≠ 0 →
    ∃ c, F.divide p a b = .value c ∧ (M p).canonical c ∧
      (M p).interpret c * (M p).interpret b = (M p).interpret a
  /-- Zero is no divisor. -/
  divide_zero : ∀ p a b, (M p).canonical a → (M p).canonical b → (M p).interpret b = 0 →
    F.divide p a b = .fault .divisionByZero

/-- The laws of exact division under `M`, on canonical elements: a zero divisor
is `DivisionByZero`; a nonzero divisor that divides the dividend gives a
canonical quotient whose product with the divisor denotes the dividend; one
that does not divide it gives the result state `inexact`. -/
structure ExactDivisionLaws {P E U : Type} {K : P → Type} [∀ p, CommRing (K p)]
    (D : ExactDivisionRing P E U) (M : Model P E K) : Prop where
  /-- A divisor that divides gives the quotient. -/
  exact : ∀ p a b, (M p).canonical a → (M p).canonical b → (M p).interpret b ≠ 0 →
    (M p).interpret b ∣ (M p).interpret a →
    ∃ q, D.exactDivide p a b = .value (.exact q) ∧ (M p).canonical q ∧
      (M p).interpret a = (M p).interpret b * (M p).interpret q
  /-- A nonzero divisor that does not divide gives `inexact`. -/
  inexact : ∀ p a b, (M p).canonical a → (M p).canonical b → (M p).interpret b ≠ 0 →
    ¬(M p).interpret b ∣ (M p).interpret a → D.exactDivide p a b = .value .inexact
  /-- Zero is no divisor. -/
  divide_zero : ∀ p a b, (M p).canonical a → (M p).canonical b → (M p).interpret b = 0 →
    D.exactDivide p a b = .fault .divisionByZero

/-- The laws of the inverse of a unit under `M`, on canonical elements: a unit
gives a canonical inverse whose product with it denotes one; a nonzero element
that is not a unit gives the result state `nonUnit`; zero, when it is not a
unit, is `DivisionByZero`. In the zero ring zero is a unit, its own
inverse. -/
structure UnitInverseLaws {P E U : Type} {K : P → Type} [∀ p, CommRing (K p)]
    (R : UnitInverseRing P E U) (M : Model P E K) : Prop where
  /-- A unit has an inverse. -/
  unit : ∀ p a, (M p).canonical a → IsUnit ((M p).interpret a) →
    ∃ u, R.unitInverse p a = .value (.unit u) ∧ (M p).canonical u ∧
      (M p).interpret a * (M p).interpret u = 1
  /-- A nonzero element that is not a unit gives `nonUnit`. -/
  nonUnit : ∀ p a, (M p).canonical a → ¬IsUnit ((M p).interpret a) → (M p).interpret a ≠ 0 →
    ∃ d, R.unitInverse p a = .value (.nonUnit d)
  /-- Zero that is not a unit has no inverse. -/
  zero : ∀ p a, (M p).canonical a → ¬IsUnit ((M p).interpret a) → (M p).interpret a = 0 →
    R.unitInverse p a = .fault .divisionByZero

/-- The zero test of `R` is sound under `M`: on canonical elements, a decided
answer is correct. -/
def ZeroTestSound {P E U : Type} {K : P → Type} [∀ p, CommRing (K p)]
    (R : CoefficientRing P E U) (M : Model P E K) : Prop :=
  ∀ p a, (M p).canonical a → ∀ t, R.zeroTest p a = .value t → t.Sound ((M p).interpret a = 0)

/-- The zero test of `R` is exact under `M`: on canonical elements it answers
`zero` exactly for an element that denotes zero and `nonzero` exactly for one
that does not, so it always decides and never fails. -/
structure ZeroTestExact {P E U : Type} {K : P → Type} [∀ p, CommRing (K p)]
    (R : CoefficientRing P E U) (M : Model P E K) : Prop where
  /-- `zero` exactly for zero. -/
  zero : ∀ p a, (M p).canonical a → (R.zeroTest p a = .value .zero ↔ (M p).interpret a = 0)
  /-- `nonzero` exactly for a nonzero element. -/
  nonzero : ∀ p a, (M p).canonical a →
    (R.zeroTest p a = .value .nonzero ↔ (M p).interpret a ≠ 0)

end Kalyx.Spec.Fields

end
