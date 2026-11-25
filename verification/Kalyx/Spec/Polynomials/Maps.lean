module

public import Kalyx.Spec.Polynomials.Basic
public import Kalyx.Spec.Fields.Maps
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Polynomials: maps coefficient by coefficient

A map between coefficient structures (`CoefficientMap` of the coefficient
fields, with the edges of their homomorphism graph) maps a polynomial
coefficient by coefficient (FLD-R11): the image of each coefficient, in the
stored order, becomes the coefficient of the same degree in the target, and
an image that the zero test of the target finds zero leaves no term. When the
map finds a coefficient outside its domain, the polynomial is outside the
domain too: the result state `notInDomain`, which is not a fault. The map of
a polynomial reaches the target only through the methods of its coefficient
ring, the zero test and the one writer of the terms; it reads no limits, and
the checks and charges of a request context are not part of this
specification.

The meaning of a map is a partial homomorphism `φ` of the interpretations
(`PartialHom`); `mapPoly φ` is its meaning on the polynomials of Mathlib: the
polynomial whose coefficients are the images of the coefficients, defined
exactly where every coefficient lies in the domain of `φ`. For a total
homomorphism it is `Polynomial.map`. `Poly.MapYields` relates the result of
the map of a polynomial to it, as `Model.MapYields` does for elements.
-/

@[expose] public section

namespace Kalyx.Spec.Polynomials

open Kalyx.Spec.Fields (CoefficientRing CoefficientMap MapResult Model PartialHom)

/-! ## The map of a polynomial -/

section Map

variable {P₁ E₁ P₂ E₂ : Type}

/-- The terms `(d, c)` of a list mapped by `f` from the source parent `s` to
the target parent `t`, written above `acc` in order: the image `c'` of each
coefficient, tested for zero by `R`, the coefficient ring of the target, and
written at the degree `d` when it is not zero; the first coefficient outside
the domain of `f` makes the result `notInDomain`. -/
def Poly.mapTerms (f : CoefficientMap P₁ E₁ P₂ E₂) (R : CoefficientRing P₂ E₂ Empty) (s : P₁)
    (t : P₂) : Poly E₂ → List (ℕ × E₁) → PolyResult (MapResult (Poly E₂))
  | acc, [] => .value (.mapped acc)
  | acc, (d, c) :: rest => do
    match ← PolyResult.ofOutcome (f.apply s t c) with
    | .notInDomain => pure .notInDomain
    | .mapped c' => Poly.mapTerms f R s t (← acc.appendNonzero R t d c') rest
termination_by structural _ l => l

/-- The polynomial `a` over the source parent `s` mapped by `f` into the
polynomials over the target parent `t` (FLD-R11), with `R` the coefficient
ring of the target: the image when every coefficient lies in the domain of
`f`, without the terms whose image is zero, and otherwise the result state
`notInDomain`. A fault of `f` or of the zero test ends the map and is its
result. -/
def Poly.map (f : CoefficientMap P₁ E₁ P₂ E₂) (R : CoefficientRing P₂ E₂ Empty) (s : P₁)
    (t : P₂) (a : Poly E₁) : PolyResult (MapResult (Poly E₂)) :=
  Poly.zero.mapTerms f R s t a.terms

end Map

/-! ## The meaning on the polynomials of Mathlib -/

section Meaning

variable {K L : Type} [CommRing K] [CommRing L]

/-- The inclusion of the domain of `φ` into its source. -/
def domainInclusion (φ : PartialHom K L) : φ.domain →+* K := φ.domain.subtype

open scoped Classical in
/-- A polynomial mapped coefficient by coefficient by the partial
homomorphism `φ`: defined exactly when every coefficient lies in the domain,
the polynomial over the domain that it comes from mapped by `φ`; undefined
otherwise. -/
noncomputable def mapPoly (φ : PartialHom K L) (a : Polynomial K) : Option (Polynomial L) :=
  if h : a ∈ (Polynomial.mapRingHom (domainInclusion φ)).rangeS then
    some (Polynomial.map φ.map (Classical.choose h))
  else none

end Meaning

/-- The result `o` of a map of polynomials into the polynomials over the
parent `t` denotes the outcome `r` of `mapPoly` under the interpretation `M`
of the target: `notInDomain` for the result state outside the domain, and for
an image a canonical polynomial over `t` that denotes it. Neither is a
fault. -/
def Poly.MapYields {P E : Type} {K : P → Type} [∀ p, CommRing (K p)] (M : Model P E K) (t : P)
    (o : PolyResult (MapResult (Poly E))) : MapResult (Polynomial (K t)) → Prop
  | .mapped y => ∃ e, o = .value (.mapped e) ∧ e.Canonical M t ∧ e.interpret M t = y
  | .notInDomain => o = .value .notInDomain

end Kalyx.Spec.Polynomials

end
