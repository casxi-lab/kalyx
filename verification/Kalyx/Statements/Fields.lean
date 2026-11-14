module

public import Kalyx.Spec.Fields.Maps

/-!
# Statements about the coefficient fields

The registered statements of the specification of the coefficient fields
(`Kalyx.Spec.Fields`), each a proposition named here and proved, or to be
proved, by a theorem of `Kalyx.Proofs.Fields`. They are written from the
numbered requirements of the numbers contract
(`docs/components/numbers/contract.md`), whose table of requirements and
statements names, for each requirement, the statements that state it.

The first eight are the properties of the structures: the ring and field
axioms under the interpretations in Mathlib, the divisions and inverses of
the rings that are not fields, exact zero tests, unique and complete canonical
forms, maps that preserve the operations, parallel paths that commute, and the
result state of the partial reduction of the rationals outside its domain.
The others are the positive and the negative examples of each requirement.

Some examples need a parent with given defining data:

* a prime field `𝔽_7` is the one that the constructor builds from `7`, as in
  `∃ F, PrimeField.new 7 = .built F ∧ …`, which states that the constructor
  accepts the modulus as well;
* a number field `Q(a)` is any parent whose minimal polynomial is the list
  of `x² + 1` (or of `x² - 2`), for every type of embeddings and every storage
  cost, together with the fact that the polynomial is monic and irreducible,
  so that such parents exist and the example is not empty;
* a residue ring `ℤ/n` is the parent `⟨n⟩` of a positive modulus, for every
  storage cost.
-/

@[expose] public section

namespace Kalyx.Statements.Fields

open Kalyx.Spec.Fields

/-! ## Properties -/

/-- The ring axioms (FLD-R01, FLD-R14, FLD-R15): the rationals, the integers,
the residue rings, the prime fields and the number fields satisfy the ring
laws under their interpretations in `ℚ`, `ℤ`, `ZMod n`, `ZMod p` and
`AdjoinRoot m`. The interpretation is injective on canonical elements, and
`zero`, `one`, `fromInteger`, `negate`, `add`, `subtract` and `multiply`
return canonical elements that denote the results in the commutative ring of
Mathlib, so the operations satisfy its axioms. The storage cost of the
residue rings and the number fields is any function of the parent and the
element. -/
def RingAxioms : Prop :=
  RingLaws Rationals.field.toCoefficientRing Rationals.model ∧
  RingLaws Integers.ring.toCoefficientRing Integers.model ∧
  (∀ μ : ResidueRing → ℕ → Storage,
    RingLaws (ResidueRing.ring μ).toCoefficientRing ResidueRing.model) ∧
  RingLaws PrimeField.field.toCoefficientRing PrimeField.model ∧
  ∀ (Emb : Type) [DecidableEq Emb] (μ : NumberField Emb → List ℚ → Storage),
    RingLaws (NumberField.field Emb μ).toCoefficientRing (NumberField.model Emb)

/-- The field axioms (FLD-R02): in the rationals, the prime fields and the
number fields, the inverse of a nonzero canonical element is canonical and
its product with the element denotes one; a quotient by a nonzero divisor is
canonical and its product with the divisor denotes the dividend; and the
inverse of zero and every quotient by zero are `DivisionByZero`. -/
def FieldAxioms : Prop :=
  FieldLaws Rationals.field Rationals.model ∧
  FieldLaws PrimeField.field PrimeField.model ∧
  ∀ (Emb : Type) [DecidableEq Emb] (μ : NumberField Emb → List ℚ → Storage),
    FieldLaws (NumberField.field Emb μ) (NumberField.model Emb)

/-- The divisions and inverses of the rings that are not fields (FLD-R14,
FLD-R15). In the integers, exact division gives the quotient when a nonzero
divisor divides the dividend, the result state `inexact` when it does not,
and `DivisionByZero` for a zero divisor. In a residue ring `ℤ/n`, a canonical
residue `a` is a unit exactly when `gcd(a, n) = 1`; a unit has an inverse
whose product with it is one; a nonzero residue that is not a unit gives the
result state `nonUnit d` with `d = gcd(a, n)`, a proper factor of `n`; the
inverse of zero is `DivisionByZero` for `n > 1`; and in `ℤ/1` zero is a unit,
its own inverse. -/
def RingDivisionAndInverse : Prop :=
  ExactDivisionLaws Integers.ring Integers.model ∧
  ∀ μ : ResidueRing → ℕ → Storage,
    UnitInverseLaws (ResidueRing.ring μ) ResidueRing.model ∧
    (∀ (R : ResidueRing) (a : ℕ), a < R.modulus →
      (IsUnit (a : ZMod R.modulus) ↔ Nat.gcd a R.modulus = 1)) ∧
    (∀ (R : ResidueRing) (a : ℕ), a < R.modulus → a ≠ 0 → Nat.gcd a R.modulus ≠ 1 →
      (ResidueRing.ring μ).unitInverse R a = .value (.nonUnit (Nat.gcd a R.modulus)) ∧
      1 < Nat.gcd a R.modulus ∧ Nat.gcd a R.modulus < R.modulus) ∧
    (∀ R : ResidueRing, 1 < R.modulus →
      (ResidueRing.ring μ).unitInverse R 0 = .fault .divisionByZero) ∧
    (ResidueRing.ring μ).unitInverse ⟨1⟩ 0 = .value (.unit 0)

/-- Exact zero tests (FLD-R04, FLD-R14, FLD-R15): in the rationals, the
integers, the residue rings, the prime fields and the number fields, the zero
test of a canonical element answers `zero` exactly when the element denotes
zero and `nonzero` exactly when it does not, so it never fails and is never
undecided. -/
def ZeroTestsAreExact : Prop :=
  ZeroTestExact Rationals.field.toCoefficientRing Rationals.model ∧
  ZeroTestExact Integers.ring.toCoefficientRing Integers.model ∧
  (∀ μ : ResidueRing → ℕ → Storage,
    ZeroTestExact (ResidueRing.ring μ).toCoefficientRing ResidueRing.model) ∧
  ZeroTestExact PrimeField.field.toCoefficientRing PrimeField.model ∧
  ∀ (Emb : Type) [DecidableEq Emb] (μ : NumberField Emb → List ℚ → Storage),
    ZeroTestExact (NumberField.field Emb μ).toCoefficientRing (NumberField.model Emb)

/-- Unique and complete canonical forms (FLD-R01, FLD-R14, FLD-R15): for every
parent of the rationals, the integers, the residue rings, the prime fields and
the number fields, two canonical elements that denote the same element are
equal, and every element of the interpretation has a canonical element. That
the operations return canonical elements is part of the ring and field
axioms. -/
def CanonicalFormsAreUniqueAndComplete : Prop :=
  (∀ p, (Rationals.model p).Unique ∧ (Rationals.model p).Complete) ∧
  (∀ p, (Integers.model p).Unique ∧ (Integers.model p).Complete) ∧
  (∀ R, (ResidueRing.model R).Unique ∧ (ResidueRing.model R).Complete) ∧
  (∀ F, (PrimeField.model F).Unique ∧ (PrimeField.model F).Complete) ∧
  ∀ (Emb : Type) (F : NumberField Emb),
    (NumberField.model Emb F).Unique ∧ (NumberField.model Emb F).Complete

/-- The maps preserve the operations (FLD-R11, FLD-R20): each edge of the
homomorphism graph realizes a partial homomorphism of the interpretations, a
ring homomorphism on its domain, which therefore preserves zero, one, sums and
products there. The maps of the integers into the rationals, a prime field
and a residue ring realize the cast of `ℤ`, total homomorphisms that give the
exact image; the map of the rationals into a number field realizes
`AdjoinRoot.of m`, total as well; and the reduction of the rationals modulo
the prime `p` of a prime field is a partial homomorphism whose domain is the
rationals whose denominator `p` does not divide. -/
def MapsPreserveOperations : Prop :=
  Integers.toRationals.Realizes Integers.model Rationals.model ⟨⟩ ⟨⟩
    (PartialHom.ofRingHom (Int.castRingHom ℚ)) ∧
  (∀ F : PrimeField, Integers.toPrimeField.Realizes Integers.model PrimeField.model ⟨⟩ F
    (intResidues F.modulus)) ∧
  (∀ R : ResidueRing, Integers.toResidueRing.Realizes Integers.model ResidueRing.model ⟨⟩ R
    (intResidues R.modulus)) ∧
  (∀ F : PrimeField, Rationals.toPrimeField.PartialOn Rationals.model PrimeField.model ⟨⟩ F
    fun q => ¬F.modulus ∣ q.den) ∧
  ∀ (Emb : Type) (F : NumberField Emb),
    (Rationals.toNumberField Emb).Realizes Rationals.model (NumberField.model Emb) ⟨⟩ F
      (PartialHom.ofRingHom (AdjoinRoot.of (QPoly.toPoly F.minimal)))

/-- Parallel paths commute (FLD-R20): a ring homomorphism out of the integers
is unique, so every pair of paths that starts at the integers commutes; the
integers into a prime field through the rationals give the same outcome as
the map of the integers into it; and the integers into a number field through
the rationals give the element that its `fromInteger` builds. -/
def ParallelPathsCommute : Prop :=
  (∀ (A : Type) [Ring A] (f g : ℤ →+* A), f = g) ∧
  (∀ (F : PrimeField) (n : ℤ),
    (Integers.toRationals.andThen Rationals.toPrimeField ⟨⟩).apply ⟨⟩ F n =
      Integers.toPrimeField.apply ⟨⟩ F n) ∧
  ∀ (Emb : Type) [DecidableEq Emb] (μ : NumberField Emb → List ℚ → Storage)
    (F : NumberField Emb) (n : ℤ),
    (Integers.toRationals.andThen (Rationals.toNumberField Emb) ⟨⟩).apply ⟨⟩ F n =
      .value (.mapped ((NumberField.field Emb μ).fromInteger F n))

/-- The partial reduction gives a result state outside its domain (FLD-R11):
the reduction of the rational `q` that a fraction denotes into the prime field
of `p` never fails; it is `notInDomain` exactly when `p` divides the
denominator of `q`; and otherwise it is the canonical residue of
`num(q) · den(q)⁻¹`. -/
def ReductionOutsideItsDomain : Prop :=
  ∀ (F : PrimeField) (a : Fraction),
    (∃ r, Rationals.toPrimeField.apply ⟨⟩ F a = .value r) ∧
    (Rationals.toPrimeField.apply ⟨⟩ F a = .value .notInDomain ↔
      F.modulus ∣ a.interpret.den) ∧
    (¬F.modulus ∣ a.interpret.den →
      ∃ r, Rationals.toPrimeField.apply ⟨⟩ F a = .value (.mapped r) ∧
        (PrimeField.model F).canonical r ∧
        F.toZMod r = (a.interpret.num : ZMod F.modulus) * (a.interpret.den : ZMod F.modulus)⁻¹)

/-! ## Canonical forms (FLD-R01) -/

/-- Canonical forms, positive (FLD-R01): `2/4` reduces to `1/2`, which is
canonical, and the sum `1/4 + 1/4` is returned as `1/2`; in `Q(a)` with
`m = x² + 1`, `a · a²` is returned as `-a`, the canonical element `[0, -1]`,
a polynomial of degree below that of `m`. -/
def CanonicalFormExamples : Prop :=
  Fraction.reduce ⟨2, 4⟩ = ⟨1, 2⟩ ∧ Fraction.Reduced ⟨1, 2⟩ ∧
  Rationals.field.add ⟨⟩ ⟨1, 4⟩ ⟨1, 4⟩ = .value ⟨1, 2⟩ ∧
  QPoly.MonicIrreducible [1, 0, 1] ∧
  ∀ (Emb : Type) [DecidableEq Emb] (μ : NumberField Emb → List ℚ → Storage)
    (F : NumberField Emb), F.minimal = [1, 0, 1] →
    let K := NumberField.field Emb μ
    let a := NumberField.generator F.minimal
    (K.multiply F a a).bind (K.multiply F a) = .value [0, -1] ∧
    (NumberField.model Emb F).canonical [0, -1]

/-- Canonical forms, negative (FLD-R01): the fractions `2/4` and `1/(-2)` are
not canonical, and the residue `7` is not a canonical element of `𝔽_7`, whose
methods reject it with `OutsideDomain`. -/
def NonCanonicalRepresentatives : Prop :=
  ¬Fraction.Reduced ⟨2, 4⟩ ∧ ¬Fraction.Reduced ⟨1, -2⟩ ∧
  ∃ F, PrimeField.new 7 = .built F ∧ ¬(PrimeField.model F).canonical ⟨7⟩ ∧
    PrimeField.field.zeroTest F ⟨7⟩ = .fault .outsideDomain

/-! ## Division and inverse (FLD-R02) -/

/-- Inverses, positive (FLD-R02): `(2/3)⁻¹ = 3/2` in the rationals,
`3⁻¹ = 5` in `𝔽_7`, and `a⁻¹ = -a` in `Q(a)` with `m = x² + 1`. -/
def InverseExamples : Prop :=
  Rationals.field.inverse ⟨⟩ ⟨2, 3⟩ = .value ⟨3, 2⟩ ∧
  (∃ F, PrimeField.new 7 = .built F ∧ PrimeField.field.inverse F ⟨3⟩ = .value ⟨5⟩) ∧
  QPoly.MonicIrreducible [1, 0, 1] ∧
  ∀ (Emb : Type) [DecidableEq Emb] (μ : NumberField Emb → List ℚ → Storage)
    (F : NumberField Emb), F.minimal = [1, 0, 1] →
    (NumberField.field Emb μ).inverse F (NumberField.generator F.minimal) = .value [0, -1]

/-- Zero has no inverse, negative (FLD-R02): in the rationals, `𝔽_7` and
`Q(a)` with `m = x² + 1`, the inverse of zero and a quotient by zero are
`DivisionByZero`; in the rationals and `𝔽_7`, whose operations check bits,
it is the only outcome that the checks admit under every `maxIntegerBits`,
`0` included, since the zero test comes before the bit checks. The number
fields have no bit checks. -/
def ZeroHasNoInverse : Prop :=
  Rationals.field.inverse ⟨⟩ ⟨0, 1⟩ = .fault .divisionByZero ∧
  Rationals.field.divide ⟨⟩ ⟨1, 1⟩ ⟨0, 1⟩ = .fault .divisionByZero ∧
  (∀ (maxIntegerBits : ℕ) (o : Outcome ℚ),
    RatUnary.Admits .inv maxIntegerBits 0 o ↔ o = .fault .divisionByZero) ∧
  (∀ (maxIntegerBits : ℕ) (o : Outcome ℚ),
    RatOp.Admits .div maxIntegerBits 1 0 o ↔ o = .fault .divisionByZero) ∧
  (∃ F, PrimeField.new 7 = .built F ∧
    PrimeField.field.inverse F ⟨0⟩ = .fault .divisionByZero ∧
    PrimeField.field.divide F ⟨1⟩ ⟨0⟩ = .fault .divisionByZero ∧
    (∀ (maxIntegerBits : ℕ) (o : Outcome PrimeResidue),
      PrimeMethod.Admits maxIntegerBits F (.inverse ⟨0⟩) o ↔ o = .fault .divisionByZero) ∧
    ∀ (maxIntegerBits : ℕ) (o : Outcome PrimeResidue),
      PrimeMethod.Admits maxIntegerBits F (.divide ⟨1⟩ ⟨0⟩) o ↔ o = .fault .divisionByZero) ∧
  QPoly.MonicIrreducible [1, 0, 1] ∧
  ∀ (Emb : Type) [DecidableEq Emb] (μ : NumberField Emb → List ℚ → Storage)
    (F : NumberField Emb), F.minimal = [1, 0, 1] →
    (NumberField.field Emb μ).inverse F [] = .fault .divisionByZero ∧
    (NumberField.field Emb μ).divide F [1] [] = .fault .divisionByZero

/-! ## Integer powers (FLD-R03) -/

/-- Integer powers, positive (FLD-R03): `a⁰ = 1` for every rational, `0⁰`
included; `(-2/3)³ = -8/27`; `2⁻² = 1/4`; and under `maxExponent = 0` and
`maxIntegerBits = 1`, at the estimate of `0⁰`, its only admitted outcome is
the value `1`. -/
def PowerExamples : Prop :=
  (∀ a : ℚ, ratPowOp a 0 = .value 1) ∧
  ratPowOp (-2 / 3) 3 = .value (-8 / 27) ∧
  ratPowOp 2 (-2) = .value (1 / 4) ∧
  ∀ o : Outcome ℚ, ratPowAdmits 0 1 0 0 o ↔ o = .value 1

/-- Integer powers, negative (FLD-R03): `0⁻¹` is `DivisionByZero`, the only
admitted outcome under every `maxIntegerBits` when `maxExponent ≥ 1`; under
`maxExponent = 2`, `0⁻³` is `ResourceLimit` naming `max_exponent` and not
`DivisionByZero`, under every `maxIntegerBits`; and under
`maxIntegerBits = 3`, the power `16⁰` may report `ResourceLimit` naming
`max_integer_bits`, since the bits of its base are checked as well. -/
def PowerFailures : Prop :=
  ratPowOp 0 (-1) = .fault .divisionByZero ∧
  (∀ (maxExponent maxIntegerBits : ℕ) (o : Outcome ℚ), 1 ≤ maxExponent →
    (ratPowAdmits maxExponent maxIntegerBits 0 (-1) o ↔ o = .fault .divisionByZero)) ∧
  (∀ (maxIntegerBits : ℕ) (o : Outcome ℚ),
    ratPowAdmits 2 maxIntegerBits 0 (-3) o ↔ o = .resourceLimit .exponent) ∧
  ∀ maxExponent : ℕ, ratPowAdmits maxExponent 3 16 0 (.resourceLimit .integerBits)

/-! ## Zero tests (FLD-R04) -/

/-- Zero tests, positive (FLD-R04): in the rationals, the integers, `ℤ/9`,
`𝔽_7` and `Q(a)` with `m = x² + 1`, the zero test answers `zero` for `zero`
and `nonzero` for `one`. -/
def ZeroTestExamples : Prop :=
  Rationals.field.zeroTest ⟨⟩ (Rationals.field.zero ⟨⟩) = .value .zero ∧
  Rationals.field.zeroTest ⟨⟩ (Rationals.field.one ⟨⟩) = .value .nonzero ∧
  Integers.ring.zeroTest ⟨⟩ (Integers.ring.zero ⟨⟩) = .value .zero ∧
  Integers.ring.zeroTest ⟨⟩ (Integers.ring.one ⟨⟩) = .value .nonzero ∧
  (∀ μ : ResidueRing → ℕ → Storage,
    (ResidueRing.ring μ).zeroTest ⟨9⟩ ((ResidueRing.ring μ).zero ⟨9⟩) = .value .zero ∧
    (ResidueRing.ring μ).zeroTest ⟨9⟩ ((ResidueRing.ring μ).one ⟨9⟩) = .value .nonzero) ∧
  (∃ F, PrimeField.new 7 = .built F ∧
    PrimeField.field.zeroTest F (PrimeField.field.zero F) = .value .zero ∧
    PrimeField.field.zeroTest F (PrimeField.field.one F) = .value .nonzero) ∧
  QPoly.MonicIrreducible [1, 0, 1] ∧
  ∀ (Emb : Type) [DecidableEq Emb] (μ : NumberField Emb → List ℚ → Storage)
    (F : NumberField Emb), F.minimal = [1, 0, 1] →
    let K := NumberField.field Emb μ
    K.zeroTest F (K.zero F) = .value .zero ∧ K.zeroTest F (K.one F) = .value .nonzero

/-- Zero tests, negative (FLD-R04): elements built as nonzero expressions that
are zero answer `zero`: `a² + 1` in `Q(a)` with `m = x² + 1`, and the image of
`7` in `𝔽_7`. -/
def ZeroTestsOfHiddenZeros : Prop :=
  (∃ F, PrimeField.new 7 = .built F ∧
    PrimeField.field.zeroTest F (PrimeField.field.fromInteger F 7) = .value .zero) ∧
  QPoly.MonicIrreducible [1, 0, 1] ∧
  ∀ (Emb : Type) [DecidableEq Emb] (μ : NumberField Emb → List ℚ → Storage)
    (F : NumberField Emb), F.minimal = [1, 0, 1] →
    let K := NumberField.field Emb μ
    let a := NumberField.generator F.minimal
    ((K.multiply F a a).bind fun s => K.add F s (K.one F)).bind (K.zeroTest F) = .value .zero

/-! ## Number-field compatibility (FLD-R05) -/

/-- Compatible number fields, positive (FLD-R05): two number-field parents are
the same exactly when their defining data, the minimal polynomial and the
embedding, are equal; so two parents built separately from the same data,
`m = x² + 1` and one embedding, are the same parent, and the sum of the
generator of one and the one of the other is `a + 1`. -/
def EqualNumberFieldsCombine : Prop :=
  (∀ (Emb : Type) [DecidableEq Emb] (μ : NumberField Emb → List ℚ → Storage)
    (F G : NumberField Emb),
    (NumberField.field Emb μ).sameParent F G = true ↔
      F.minimal = G.minimal ∧ F.embedding = G.embedding) ∧
  QPoly.MonicIrreducible [1, 0, 1] ∧
  ∀ (Emb : Type) [DecidableEq Emb] (μ : NumberField Emb → List ℚ → Storage)
    (F G : NumberField Emb), F.minimal = [1, 0, 1] → G.minimal = [1, 0, 1] →
    F.embedding = G.embedding →
    let K := NumberField.field Emb μ
    K.sameParent F G = true ∧
    K.paired K.add (F, NumberField.generator F.minimal) (G, K.one G) = .value (F, [1, 1])

/-- Incompatible number fields, negative (FLD-R05): the elements of `Q(a)`
with `m = x² + 1` and of `Q(a)` with `m = x² - 2` are a `VariableMismatch` when
added, and still when the divisor is the zero of the other field, since the
mismatch comes before the zero divisor; and two fields with the same
polynomial and different embeddings are incompatible, so the product of their
generators is a `VariableMismatch` too. -/
def DifferentNumberFieldsMismatch : Prop :=
  QPoly.MonicIrreducible [1, 0, 1] ∧ QPoly.MonicIrreducible [-2, 0, 1] ∧
  (∀ (Emb : Type) [DecidableEq Emb] (μ : NumberField Emb → List ℚ → Storage)
    (F G : NumberField Emb), F.minimal = [1, 0, 1] → G.minimal = [-2, 0, 1] →
    let K := NumberField.field Emb μ
    K.paired K.add (F, NumberField.generator F.minimal) (G, NumberField.generator G.minimal) =
      .fault .variableMismatch ∧
    K.paired K.divide (F, NumberField.generator F.minimal) (G, K.zero G) =
      .fault .variableMismatch) ∧
  ∀ (Emb : Type) [DecidableEq Emb] (μ : NumberField Emb → List ℚ → Storage)
    (F G : NumberField Emb), F.minimal = G.minimal → F.embedding ≠ G.embedding →
    let K := NumberField.field Emb μ
    K.paired K.multiply (F, NumberField.generator F.minimal) (G, NumberField.generator G.minimal) =
      .fault .variableMismatch

/-! ## Homomorphisms (FLD-R11) -/

/-- Maps, positive (FLD-R11): the reduction of the rationals into `𝔽_7` maps
`1/2` to `4`, and the map of the rationals into `Q(a)` with `m = x² + 1` maps
`1/2` to the constant `1/2`. -/
def MapExamples : Prop :=
  (∃ F, PrimeField.new 7 = .built F ∧
    Rationals.toPrimeField.apply ⟨⟩ F ⟨1, 2⟩ = .value (.mapped ⟨4⟩)) ∧
  QPoly.MonicIrreducible [1, 0, 1] ∧
  ∀ (Emb : Type) (F : NumberField Emb), F.minimal = [1, 0, 1] →
    (Rationals.toNumberField Emb).apply ⟨⟩ F ⟨1, 2⟩ = .value (.mapped [1 / 2])

/-- Maps, negative (FLD-R11): the reduction of the rationals into `𝔽_7` gives
`1/7` the result state `notInDomain`, a value and not an error. -/
def ReductionOfOneSeventh : Prop :=
  ∃ F, PrimeField.new 7 = .built F ∧
    Rationals.toPrimeField.apply ⟨⟩ F ⟨1, 7⟩ = .value .notInDomain

/-! ## Bit checks (FLD-R12) -/

/-- Bit checks, positive (FLD-R12): under `maxIntegerBits = 4`, the bound of
the product `(1/2) · (1/2)`, the larger of the sums of the bits of the
numerators and of the denominators, is within the limit, so the value `1/4`
is the only admitted outcome; the coefficient field returns `1/4`. -/
def ProductWithinBitLimit : Prop :=
  (∀ o : Outcome ℚ, RatOp.Admits .mul 4 (1 / 2) (1 / 2) o ↔ o = .value (1 / 4)) ∧
  Rationals.field.multiply ⟨⟩ ⟨1, 2⟩ ⟨1, 2⟩ = .value ⟨1, 4⟩

/-- Bit checks, negative (FLD-R12): under `maxIntegerBits = 3` the same
product may report `ResourceLimit` naming `max_integer_bits`, in the form of
the checks that may report; and under `maxIntegerBits = 0` the quotient `1/0`
is still `DivisionByZero`, its only admitted outcome. -/
def ProductBeyondBitLimit : Prop :=
  RatOp.Admits .mul 3 (1 / 2) (1 / 2) (.resourceLimit .integerBits) ∧
  ∀ o : Outcome ℚ, RatOp.Admits .div 0 1 0 o ↔ o = .fault .divisionByZero

/-! ## The integers (FLD-R14) -/

/-- Integers, positive (FLD-R14): `6 / 3` is exactly `2`, and the units, the
integers by which `1` divides exactly, are `1` and `-1`. -/
def IntegerDivisionExamples : Prop :=
  Integers.ring.exactDivide ⟨⟩ 6 3 = .value (.exact 2) ∧
  ∀ u : ℤ, (∃ v, Integers.ring.exactDivide ⟨⟩ 1 u = .value (.exact v)) ↔ u = 1 ∨ u = -1

/-- Integers, negative (FLD-R14): `7 / 2` is the result state `inexact`, not an
error and not a rounded quotient; `0 / 0` is `DivisionByZero`; and `2` is not
a unit, since `1 / 2` is `inexact`. -/
def IntegerDivisionFailures : Prop :=
  Integers.ring.exactDivide ⟨⟩ 7 2 = .value .inexact ∧
  Integers.ring.exactDivide ⟨⟩ 0 0 = .fault .divisionByZero ∧
  Integers.ring.exactDivide ⟨⟩ 1 2 = .value .inexact

/-! ## Residue rings (FLD-R15) -/

/-- Residue rings, positive (FLD-R15): `2⁻¹ = 5` in `ℤ/9`; `ℤ/1` is the zero
ring, where `one` is `zero`, and zero is a unit with the inverse `0`. -/
def ResidueInverseExamples : Prop :=
  ∀ μ : ResidueRing → ℕ → Storage,
    (ResidueRing.ring μ).unitInverse ⟨9⟩ 2 = .value (.unit 5) ∧
    (ResidueRing.ring μ).one ⟨1⟩ = (ResidueRing.ring μ).zero ⟨1⟩ ∧
    (ResidueRing.ring μ).unitInverse ⟨1⟩ 0 = .value (.unit 0)

/-- Residue rings, negative (FLD-R15): in `ℤ/9`, `6` is not a unit, with the
factor `3`, and the inverse of zero is `DivisionByZero`; the modulus `0` is
rejected, which the library reports as `OutsideDomain`; and residues of `ℤ/6`
and `ℤ/9` are a `VariableMismatch` when added, and when divided by a zero
divisor, since the mismatch comes first. -/
def ResidueFailures : Prop :=
  (∀ μ : ResidueRing → ℕ → Storage,
    (ResidueRing.ring μ).unitInverse ⟨9⟩ 6 = .value (.nonUnit 3) ∧
    (ResidueRing.ring μ).unitInverse ⟨9⟩ 0 = .fault .divisionByZero) ∧
  ResidueRing.new 0 = .rejected ∧
  ResidueTagged.ringOp .add ⟨⟨6⟩, 1⟩ ⟨⟨9⟩, 1⟩ = .fault .variableMismatch ∧
  ResidueTagged.div ⟨⟨6⟩, 1⟩ ⟨⟨9⟩, 0⟩ = .fault .variableMismatch

/-! ## Parents and the homomorphism graph (FLD-R20) -/

/-- Parallel paths and the agreement of `ℤ/p` with `𝔽_p`, positive
(FLD-R20): `-3` maps to `4` in `𝔽_7` through the rationals and directly, and
`3⁻¹ = 5` both in `ℤ/7` and in `𝔽_7`. For every prime field and the residue
ring of the same modulus, sums, differences and products of residues below
the modulus agree, and so do the inverses of nonzero residues, all of which
are units. -/
def IntegerPathsAndResiduesAgree : Prop :=
  (∃ F, PrimeField.new 7 = .built F ∧
    (Integers.toRationals.andThen Rationals.toPrimeField ⟨⟩).apply ⟨⟩ F (-3) =
      .value (.mapped ⟨4⟩) ∧
    Integers.toPrimeField.apply ⟨⟩ F (-3) = .value (.mapped ⟨4⟩) ∧
    PrimeField.field.inverse F ⟨3⟩ = .value ⟨5⟩) ∧
  (∀ μ : ResidueRing → ℕ → Storage, (ResidueRing.ring μ).unitInverse ⟨7⟩ 3 = .value (.unit 5)) ∧
  ∀ (μ : ResidueRing → ℕ → Storage) (R : ResidueRing) (F : PrimeField),
    (R.modulus : ℕ) = F.modulus → ∀ a b : ℕ, a < F.modulus → b < F.modulus →
    (ResidueRing.ring μ).add R a b = (PrimeField.field.add F ⟨a⟩ ⟨b⟩).map PrimeResidue.value ∧
    (ResidueRing.ring μ).subtract R a b =
      (PrimeField.field.subtract F ⟨a⟩ ⟨b⟩).map PrimeResidue.value ∧
    (ResidueRing.ring μ).multiply R a b =
      (PrimeField.field.multiply F ⟨a⟩ ⟨b⟩).map PrimeResidue.value ∧
    (a ≠ 0 → (ResidueRing.ring μ).unitInverse R a =
      (PrimeField.field.inverse F ⟨a⟩).map fun u => .unit u.value)

/-- Residue rings and prime fields are different parents, negative (FLD-R20):
parents are compared by their defining data only, a residue ring by its
modulus and a prime field by its prime, and the two structures have parents
of different types, so that no operation takes an element of `ℤ/7` and one of
`𝔽_7` together; in both, the inverse of zero is `DivisionByZero`. -/
def ResidueRingsAndPrimeFieldsDiffer : Prop :=
  (∀ μ : ResidueRing → ℕ → Storage, SameParentLaw (ResidueRing.ring μ).toCoefficientRing) ∧
  SameParentLaw PrimeField.field.toCoefficientRing ∧
  ResidueRing ≠ PrimeField ∧
  (∀ μ : ResidueRing → ℕ → Storage,
    (ResidueRing.ring μ).unitInverse ⟨7⟩ 0 = .fault .divisionByZero) ∧
  ∃ F, PrimeField.new 7 = .built F ∧ PrimeField.field.inverse F ⟨0⟩ = .fault .divisionByZero

end Kalyx.Statements.Fields

end
