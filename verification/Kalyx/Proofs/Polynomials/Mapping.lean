module

public import Kalyx.Proofs.Polynomials.Operations

/-!
# Maps of polynomials coefficient by coefficient

An unregistered helper module of the proofs about the univariate polynomials;
it proves no registered statement. It holds:

* the meaning `mapPoly` of a map on the polynomials of Mathlib: it is defined
  exactly when every coefficient lies in the domain (`mapPoly_none_iff`), and
  then it is the image of the polynomial over the domain that the polynomial
  comes from (`mapPoly_eq_some_iff'`), whose coefficients are the images of
  the coefficients (`mapPoly_eq_some_iff`); it preserves sums and products
  (`mapPoly_add`, `mapPoly_mul`), and a total homomorphism maps every
  polynomial by `Polynomial.map` (`mapPoly_ofRingHom`);
* the map of a canonical polynomial by a map of coefficients that realizes a
  partial homomorphism, into a coefficient ring that is exact: each image is
  written after its zero test above the images before it, so the result is a
  canonical polynomial that denotes the image of the polynomial over the
  domain, or `notInDomain` at the first coefficient outside the domain
  (`map_spec`).
-/

namespace Kalyx.Proofs.Polynomials.Mapping

open Kalyx.Spec.Fields Kalyx.Spec.Polynomials Kalyx.Statements.Polynomials Polynomial
open Kalyx.Proofs.Polynomials.Canonical Kalyx.Proofs.Polynomials.Operations

/-! ## The meaning on the polynomials of Mathlib -/

section Meaning

variable {K L : Type} [CommRing K] [CommRing L] (φ : PartialHom K L)

/-- A polynomial comes from the domain exactly when all its coefficients lie
in it. -/
public theorem mem_rangeS_iff (A : Polynomial K) :
    A ∈ (mapRingHom (domainInclusion φ)).rangeS ↔ ∀ n, A.coeff n ∈ φ.domain := by
  rw [mem_map_rangeS]
  refine forall_congr' fun n => ?_
  simp [domainInclusion, RingHom.mem_rangeS]

/-- The map of a polynomial is undefined exactly when a coefficient lies
outside the domain. -/
public theorem mapPoly_none_iff (A : Polynomial K) :
    mapPoly φ A = none ↔ ∃ n, A.coeff n ∉ φ.domain := by
  rw [← not_forall, ← mem_rangeS_iff]
  unfold mapPoly
  by_cases h : A ∈ (mapRingHom (domainInclusion φ)).rangeS <;> simp [h]

/-- The map of a polynomial is the image of the polynomial over the domain
that it comes from. -/
public theorem mapPoly_eq_some_iff' (A : Polynomial K) (B : Polynomial L) :
    mapPoly φ A = some B ↔
      ∃ q : Polynomial φ.domain, q.map (domainInclusion φ) = A ∧ q.map φ.map = B := by
  constructor
  · intro h
    unfold mapPoly at h
    split at h
    · rename_i hp
      exact ⟨Classical.choose hp, Classical.choose_spec hp, Option.some.inj h⟩
    · simp at h
  · rintro ⟨q, rfl, rfl⟩
    have hp : q.map (domainInclusion φ) ∈ (mapRingHom (domainInclusion φ)).rangeS := ⟨q, rfl⟩
    unfold mapPoly
    simp only [hp, ↓reduceDIte]
    congr 2
    exact Polynomial.map_injective _ Subtype.val_injective (Classical.choose_spec hp)

/-- The map of a polynomial, coefficient by coefficient: defined exactly when
every coefficient lies in the domain, with the image of each coefficient. -/
public theorem mapPoly_eq_some_iff (A : Polynomial K) (B : Polynomial L) :
    mapPoly φ A = some B ↔
      ∃ h : ∀ n, A.coeff n ∈ φ.domain, ∀ n, B.coeff n = φ.map ⟨A.coeff n, h n⟩ := by
  rw [mapPoly_eq_some_iff']
  constructor
  · rintro ⟨q, rfl, rfl⟩
    refine ⟨fun n => by simp [coeff_map, domainInclusion], fun n => ?_⟩
    rw [coeff_map]
    congr 1
    ext
    simp [coeff_map, domainInclusion]
  · rintro ⟨h, hB⟩
    obtain ⟨q, hq⟩ := (mem_rangeS_iff φ A).2 h
    refine ⟨q, hq, ?_⟩
    ext n
    rw [coeff_map, hB n]
    congr 1
    ext
    show (q.coeff n : K) = A.coeff n
    rw [← hq, coe_mapRingHom, coeff_map]
    rfl

/-- The map of polynomials preserves sums. -/
public theorem mapPoly_add {A B : Polynomial K} {A' B' : Polynomial L}
    (hA : mapPoly φ A = some A') (hB : mapPoly φ B = some B') :
    mapPoly φ (A + B) = some (A' + B') := by
  obtain ⟨p, rfl, rfl⟩ := (mapPoly_eq_some_iff' φ A A').1 hA
  obtain ⟨q, rfl, rfl⟩ := (mapPoly_eq_some_iff' φ B B').1 hB
  exact (mapPoly_eq_some_iff' φ _ _).2 ⟨p + q, by simp, by simp⟩

/-- The map of polynomials preserves products. -/
public theorem mapPoly_mul {A B : Polynomial K} {A' B' : Polynomial L}
    (hA : mapPoly φ A = some A') (hB : mapPoly φ B = some B') :
    mapPoly φ (A * B) = some (A' * B') := by
  obtain ⟨p, rfl, rfl⟩ := (mapPoly_eq_some_iff' φ A A').1 hA
  obtain ⟨q, rfl, rfl⟩ := (mapPoly_eq_some_iff' φ B B').1 hB
  exact (mapPoly_eq_some_iff' φ _ _).2 ⟨p * q, by simp, by simp⟩

/-- A total homomorphism maps every polynomial by `Polynomial.map`. -/
public theorem mapPoly_ofRingHom (g : K →+* L) (A : Polynomial K) :
    mapPoly (PartialHom.ofRingHom g) A = some (A.map g) :=
  (mapPoly_eq_some_iff _ A _).2 ⟨fun _ => Subring.mem_top _, fun n => by
    rw [coeff_map]
    rfl⟩

end Meaning

/-! ## The map of a canonical polynomial -/

section Map

variable {P₁ E₁ P₂ E₂ : Type} {K : P₁ → Type} {L : P₂ → Type} [∀ s, CommRing (K s)]
  [∀ t, CommRing (L t)] {f : CoefficientMap P₁ E₁ P₂ E₂} {R : CoefficientRing P₂ E₂ Empty}
  {M₁ : Model P₁ E₁ K} {M₂ : Model P₂ E₂ L} {s : P₁} {t : P₂} {φ : PartialHom (K s) (L t)}

/-- A canonical coefficient in the domain maps to a canonical element that
denotes its image. -/
private theorem apply_of_mem (hf : f.Realizes M₁ M₂ s t φ) {c : E₁}
    (hc : (M₁ s).canonical c) (h : (M₁ s).interpret c ∈ φ.domain) :
    ∃ c', f.apply s t c = .value (.mapped c') ∧ (M₂ t).canonical c' ∧
      (M₂ t).interpret c' = φ.map ⟨_, h⟩ := by
  have := hf c hc
  simp only [PartialHom.apply, h, ↓reduceDIte] at this
  exact this

/-- A canonical coefficient outside the domain maps to `notInDomain`. -/
private theorem apply_of_not_mem (hf : f.Realizes M₁ M₂ s t φ) {c : E₁}
    (hc : (M₁ s).canonical c) (h : (M₁ s).interpret c ∉ φ.domain) :
    f.apply s t c = .value .notInDomain := by
  have := hf c hc
  simp only [PartialHom.apply, h, ↓reduceDIte] at this
  exact this

/-- The loop of the map over the terms of a canonical list, written above a
canonical polynomial below them: when every coefficient lies in the domain, a
canonical polynomial that denotes the polynomial plus the image of the
polynomial over the domain that the list comes from; otherwise
`notInDomain`. -/
private theorem mapTerms_spec (hR : ExactRing R M₂) (hf : f.Realizes M₁ M₂ s t φ) :
    ∀ (l : List (ℕ × E₁)) (acc : Poly E₂), acc.Canonical M₂ t → (⟨l⟩ : Poly E₁).Canonical M₁ s →
      (∀ x ∈ acc.terms, ∀ y ∈ l, x.1 < y.1) →
      ((∀ x ∈ l, (M₁ s).interpret x.2 ∈ φ.domain) →
        ∃ e, ∃ q : Polynomial φ.domain, Poly.mapTerms f R s t acc l = .value (.mapped e) ∧
          e.Canonical M₂ t ∧ q.map (domainInclusion φ) = (⟨l⟩ : Poly E₁).interpret M₁ s ∧
          e.interpret M₂ t = acc.interpret M₂ t + q.map φ.map) ∧
      ((∃ x ∈ l, (M₁ s).interpret x.2 ∉ φ.domain) →
        Poly.mapTerms f R s t acc l = .value .notInDomain) := by
  intro l
  induction l with
  | nil =>
    refine fun acc hacc _ _ => ⟨fun _ => ⟨acc, 0, rfl, hacc, by simp, by simp⟩, ?_⟩
    rintro ⟨x, hx, -⟩
    simp at hx
  | cons x l ih =>
    intro acc hacc hl hbelow
    obtain ⟨d, c⟩ := x
    obtain ⟨hlt, ⟨hc, -⟩, hl'⟩ := (canonical_cons_iff M₁ s (d, c) l).1 hl
    by_cases hd : (M₁ s).interpret c ∈ φ.domain
    · obtain ⟨c', hfc, hc', hc'i⟩ := apply_of_mem hf hc hd
      obtain ⟨b, hb, hbc, hbi, hble⟩ :=
        appendNonzero_spec (R := R) hR.2 hacc (fun x hx => hbelow x hx _ List.mem_cons_self) hc'
      have key : Poly.mapTerms f R s t acc ((d, c) :: l) = Poly.mapTerms f R s t b l := by
        simp only [Poly.mapTerms, hfc, bind_eq_bind, ofOutcome_value, bind_value, hb]
      obtain ⟨ih₁, ih₂⟩ :=
        ih b hbc hl' fun x hx y hy => lt_of_le_of_lt (hble x hx) (hlt y hy)
      refine ⟨fun hall => ?_, fun ⟨x, hx, hxd⟩ => ?_⟩
      · obtain ⟨e, q, he, hec, hq, hei⟩ := ih₁ fun x hx => hall x (List.mem_cons_of_mem _ hx)
        refine ⟨e, monomial d ⟨_, hd⟩ + q, key ▸ he, hec, ?_, ?_⟩
        · rw [Polynomial.map_add, map_monomial, hq, interpret_cons]
          rfl
        · rw [hei, hbi, Polynomial.map_add, map_monomial, hc'i, add_assoc]
      · rw [key]
        rcases List.mem_cons.1 hx with rfl | hx
        · exact absurd hd hxd
        · exact ih₂ ⟨x, hx, hxd⟩
    · have hfc := apply_of_not_mem hf hc hd
      have key : Poly.mapTerms f R s t acc ((d, c) :: l) = .value .notInDomain := by
        simp only [Poly.mapTerms, hfc, bind_eq_bind, ofOutcome_value, bind_value, pure_eq_value]
      exact ⟨fun hall => absurd (hall _ List.mem_cons_self) hd, fun _ => key⟩

/-- The map of a canonical polynomial by a map that realizes `φ`, into a
coefficient ring that is exact, denotes the outcome of `mapPoly`. -/
public theorem map_spec (hR : ExactRing R M₂) (hf : f.Realizes M₁ M₂ s t φ) {a : Poly E₁}
    (ha : a.Canonical M₁ s) :
    Poly.MapYields M₂ t (Poly.map f R s t a)
      (MapResult.ofOption (mapPoly φ (a.interpret M₁ s))) := by
  obtain ⟨h₁, h₂⟩ := mapTerms_spec hR hf a.terms Poly.zero (canonical_zero M₂ t) ha
    (by simp [Poly.zero])
  unfold Poly.map
  by_cases hall : ∀ x ∈ a.terms, (M₁ s).interpret x.2 ∈ φ.domain
  · obtain ⟨e, q, he, hec, hq, hei⟩ := h₁ hall
    rw [mk_terms] at hq
    rw [(mapPoly_eq_some_iff' φ _ _).2 ⟨q, hq, rfl⟩]
    exact ⟨e, he, hec, by rw [hei, interpret_zero, zero_add]⟩
  · push Not at hall
    obtain ⟨⟨d, c⟩, hx, hxd⟩ := hall
    have hnone : mapPoly φ (a.interpret M₁ s) = none :=
      (mapPoly_none_iff φ _).2 ⟨d, by rwa [coeff_interpret_of_mem M₁ s ha hx]⟩
    rw [hnone]
    exact h₂ ⟨(d, c), hx, hxd⟩

end Map

end Kalyx.Proofs.Polynomials.Mapping
