module

public import Kalyx.Spec.Fields.Residues
public import Kalyx.Spec.Fields.NumberField

/-!
# Maps between the coefficient structures

A map between coefficient structures sends the elements of a source parent to
those of a target parent (numbers contract, FLD-R11 and FLD-R20). Its meaning
is a partial homomorphism (`PartialHom`) of the interpretations of the two
structures: a ring homomorphism from a subring of the source, its domain, into
the target. A total homomorphism, such as the cast of the integers into a ring,
is a partial one whose domain is the whole source (`PartialHom.ofRingHom`).
An element outside the domain is the result state `notInDomain` (`MapResult`),
not an error: the outcome of a map is never a fault (`PartialHom.applyOp`).

`CoefficientMap` is the trait of the maps over two parents: `apply s t x` is
the outcome of the element `x` of the source parent `s` in the target parent
`t`. A map realizes a partial homomorphism `φ` (`CoefficientMap.Realizes`)
when, on every canonical element, its outcome is `notInDomain` exactly where
`φ` is undefined, and otherwise a canonical element that denotes the image
under `φ`. The edges of the homomorphism graph in this specification are
computable maps on the stored elements:

* the total maps out of the integers, `n ↦ n · 1`: into the rationals
  (`Integers.toRationals`), which realizes the cast of `ℤ` into `ℚ`, into a
  prime field (`Integers.toPrimeField`) and into a residue ring
  (`Integers.toResidueRing`), which realize the reduction `intResidues`;
* the reduction of the rationals modulo the prime `p` of a prime field
  (`Rationals.toPrimeField`), a partial map: a rational `a/b` in lowest terms
  whose denominator `p` does not divide maps to `a b⁻¹` (`ratReduce`), and one
  whose denominator `p` divides is outside its domain;
* the total map of the rationals into a number field
  (`Rationals.toNumberField`): a rational is the constant polynomial in the
  generator, which realizes `AdjoinRoot.of m`.

A path through a middle parent is the composition of two maps
(`CoefficientMap.andThen`); parallel paths, such as the integers into a prime
field directly and through the rationals, are compared by their outcomes. The
maps have no checks of the limits in this specification, and the map of
polynomials coefficient by coefficient is not part of it.
-/

@[expose] public section

namespace Kalyx.Spec.Fields

/-! ## Partial homomorphisms -/

/-- A ring homomorphism from a subring of `K` into `L`. -/
structure PartialHom (K L : Type) [CommRing K] [CommRing L] where
  /-- The domain, a subring of `K`. -/
  domain : Subring K
  /-- The homomorphism on the domain. -/
  map : domain →+* L

/-- The outcome of a map: an image, or the result state that the element lies
outside the domain of the map, which is not an error. -/
inductive MapResult (α : Type) where
  /-- The element maps to `value`. -/
  | mapped (value : α)
  /-- The element lies outside the domain. -/
  | notInDomain
  deriving DecidableEq, Repr

/-- The map outcome of an optional value. -/
def MapResult.ofOption {α : Type} : Option α → MapResult α
  | some a => .mapped a
  | none => .notInDomain

/-- The map outcome with `f` applied to its image; the result state outside
the domain is kept. -/
def MapResult.map {α β : Type} (f : α → β) : MapResult α → MapResult β
  | .mapped a => .mapped (f a)
  | .notInDomain => .notInDomain

namespace PartialHom

variable {K L : Type} [CommRing K] [CommRing L]

open scoped Classical in
/-- The value of the homomorphism, or `none` outside its domain. -/
noncomputable def apply (φ : PartialHom K L) (x : K) : Option L :=
  if h : x ∈ φ.domain then some (φ.map ⟨x, h⟩) else none

/-- A total homomorphism is a partial one with the whole ring as domain. -/
def ofRingHom (f : K →+* L) : PartialHom K L where
  domain := ⊤
  map := f.comp (Subring.subtype ⊤)

/-- `apply` in the operation layer: an element outside the domain is the
result state `notInDomain`, never a fault. -/
noncomputable def applyOp (φ : PartialHom K L) (x : K) : Outcome (MapResult L) :=
  .value (MapResult.ofOption (φ.apply x))

end PartialHom

/-- The reduction of the integers onto `ZMod n`, a total homomorphism for
every `n`: the meaning of the maps of the integers into the prime field of a
prime `n` and into the residue ring `ℤ/n`. -/
def intResidues (n : ℕ) : PartialHom ℤ (ZMod n) :=
  PartialHom.ofRingHom (Int.castRingHom (ZMod n))

/-! ## Maps over two parents -/

/-- A map between coefficient structures, the trait of the maps over two
parents, from the elements `E₁` of the parents `P₁` to the elements `E₂` of
the parents `P₂`: `apply s t x` is the outcome of the element `x` of the
source parent `s` in the target parent `t`, an image or the result state
`notInDomain`. As the methods of the coefficient rings, a map assumes that its
element belongs to the source parent. -/
structure CoefficientMap (P₁ E₁ P₂ E₂ : Type) where
  /-- The outcome of an element of the source parent in the target parent. -/
  apply : P₁ → P₂ → E₁ → Outcome (MapResult E₂)

/-- The path of the map `f` into the middle parent `m`, followed by the map
`g` out of it: the outcome of `g` on the image under `f`. An element outside
the domain of `f` is outside the domain of the path. -/
def CoefficientMap.andThen {P₁ E₁ P₂ E₂ P₃ E₃ : Type} (f : CoefficientMap P₁ E₁ P₂ E₂)
    (g : CoefficientMap P₂ E₂ P₃ E₃) (m : P₂) : CoefficientMap P₁ E₁ P₃ E₃ where
  apply s t x := (f.apply s m x).bind fun
    | .mapped y => g.apply m t y
    | .notInDomain => .value .notInDomain

/-- The outcome `o` of a map denotes the outcome `r` of a homomorphism in the
target parent `t` under the interpretation `M`: `notInDomain` for the result
state outside the domain, and for an image a canonical element that denotes
it. Neither is a fault. -/
def Model.MapYields {P E : Type} {K : P → Type} (M : Model P E K) (t : P)
    (o : Outcome (MapResult E)) : MapResult (K t) → Prop
  | .mapped y => ∃ e, o = .value (.mapped e) ∧ (M t).canonical e ∧ (M t).interpret e = y
  | .notInDomain => o = .value .notInDomain

/-- The map `f` from the parent `s` to the parent `t` realizes the partial
homomorphism `φ` of their interpretations under `M₁` and `M₂`: on every
canonical element `x`, the outcome of `f` is `notInDomain` when the element
that `x` denotes lies outside the domain of `φ`, and otherwise a canonical
element that denotes its image under `φ`. -/
def CoefficientMap.Realizes {P₁ E₁ P₂ E₂ : Type} {K : P₁ → Type} {L : P₂ → Type}
    [∀ s, CommRing (K s)] [∀ t, CommRing (L t)] (f : CoefficientMap P₁ E₁ P₂ E₂)
    (M₁ : Model P₁ E₁ K) (M₂ : Model P₂ E₂ L) (s : P₁) (t : P₂)
    (φ : PartialHom (K s) (L t)) : Prop :=
  ∀ x, (M₁ s).canonical x →
    M₂.MapYields t (f.apply s t x) (MapResult.ofOption (φ.apply ((M₁ s).interpret x)))

/-- The map `f` from the parent `s` to the parent `t` is, under `M₁` and
`M₂`, a partial homomorphism whose domain is the set `D` of elements of the
interpretation of `s`: it realizes such a partial homomorphism. -/
def CoefficientMap.PartialOn {P₁ E₁ P₂ E₂ : Type} {K : P₁ → Type} {L : P₂ → Type}
    [∀ s, CommRing (K s)] [∀ t, CommRing (L t)] (f : CoefficientMap P₁ E₁ P₂ E₂)
    (M₁ : Model P₁ E₁ K) (M₂ : Model P₂ E₂ L) (s : P₁) (t : P₂) (D : K s → Prop) : Prop :=
  ∃ φ : PartialHom (K s) (L t), (∀ x, x ∈ φ.domain ↔ D x) ∧ f.Realizes M₁ M₂ s t φ

/-! ## The edges of the homomorphism graph -/

/-- The map of the integers into the rationals, `n ↦ n/1`, the `fromInteger`
of the rationals. It realizes the cast of `ℤ` into `ℚ`. -/
def Integers.toRationals : CoefficientMap Integers ℤ Rationals Fraction where
  apply _ t n := .value (.mapped (Rationals.field.fromInteger t n))

/-- The map of the integers into a prime field `𝔽_p`, the `fromInteger` of the
prime fields: the Euclidean remainder of `n` by `p`. It realizes
`intResidues p`. -/
def Integers.toPrimeField : CoefficientMap Integers ℤ PrimeField PrimeResidue where
  apply _ F n := .value (.mapped (PrimeField.field.fromInteger F n))

/-- The map of the integers into a residue ring `ℤ/n`: the least nonnegative
residue of `k`, as the `fromInteger` of the residue rings. It realizes
`intResidues n`. -/
def Integers.toResidueRing : CoefficientMap Integers ℤ ResidueRing ℕ where
  apply _ R k := .value (.mapped (k : ZMod R.modulus).val)

/-- The reduction of a rational modulo `p` where it is defined: undefined when
`p` divides the denominator of the rational in lowest terms, and otherwise the
class of the numerator times the inverse of the class of the denominator. For
a prime `p`, the class of a denominator that `p` does not divide is a unit, and
`ZMod`'s inverse is its inverse. -/
def ratReduce (p : ℕ) (q : ℚ) : Option (ZMod p) :=
  if p ∣ q.den then none else some ((q.num : ZMod p) * (q.den : ZMod p)⁻¹)

/-- The reduction modulo `p` in the operation layer: a rational whose
denominator `p` divides is the result state `notInDomain`, never a fault. -/
def ratReduceOp (p : ℕ) (q : ℚ) : Outcome (MapResult (ZMod p)) :=
  .value (MapResult.ofOption (ratReduce p q))

/-- The reduction of the rationals modulo the prime `p` of a prime field, a
partial map on the rational that a fraction denotes: the least nonnegative
residue of its reduction where `p` does not divide its denominator, and the
result state `notInDomain` where it does. Its domain is a subring of `ℚ`, the
rationals whose denominator in lowest terms is prime to `p`. -/
def Rationals.toPrimeField : CoefficientMap Rationals Fraction PrimeField PrimeResidue where
  apply _ F a := (ratReduceOp F.modulus a.interpret).map (MapResult.map F.ofZMod)

/-- The map of the rationals into the number fields with embeddings of type
`Emb`: the rational that a fraction denotes is the constant polynomial in the
generator, reduced, as the `fromInteger` of the number fields forms an
integer. It realizes `AdjoinRoot.of m` of the minimal polynomial `m`. -/
def Rationals.toNumberField (Emb : Type) :
    CoefficientMap Rationals Fraction (NumberField Emb) (List ℚ) where
  apply _ F a := .value (.mapped (NumberField.ofRat F.minimal a.interpret))

end Kalyx.Spec.Fields

end
