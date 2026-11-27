module

public import Kalyx.Proofs.Multivariate.Canonical

/-!
# Proofs of the statements about the form of the polynomials

One theorem for each registered statement of `Kalyx.Statements.Multivariate`
about the form of the polynomials, whose type is exactly that statement. They
state that the leading term, the total degree and the monic test are those of
Mathlib under every monomial order of Mathlib that agrees with the order of
the ring, and that the normalization of terms with canonical coefficients
gives the canonical form of their sum, whatever their order.

The terms of a canonical polynomial increase under the order of the ring, so
its last term is above the others under every monomial order of Mathlib that
agrees with that order, and the support of its interpretation is the set of
the vectors of its monomials: the last term gives the degree and the leading
coefficient, and the largest total degree of the monomials is the total
degree. Normalization is proved in `Kalyx.Proofs.Multivariate.Canonical`
(`normalize_yields`, `normalize_perm`).
-/

namespace Kalyx.Proofs.Multivariate

open Kalyx.Spec.Fields Kalyx.Spec.Multivariate Kalyx.Statements.Multivariate MvPolynomial
open Kalyx.Proofs.Multivariate.Canonical

variable {P E : Type} {K : P → Type} [∀ p, CommRing (K p)] {M : Model P E K} {p : P} {n : ℕ}

/-- Every term of a canonical polynomial is its last term or below it. -/
private theorem le_of_getLast? {o : OrderKind n} {a : MvPoly n E} (ha : a.Canonical M p o)
    {e : Exponents n} {c : E} (h : a.terms.getLast? = some (e, c)) :
    ∀ x ∈ a.terms, x.1 = e ∨ o.Lt x.1 e := by
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 h
  have hs := ((canonical_iff_terms M p o a).1 ha).1
  rw [hys, List.pairwise_append] at hs
  intro x hx
  rw [hys, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact .inr (hs.2.2 x hx _ List.mem_cons_self)
  · exact .inl rfl

/-- The last term of a canonical polynomial gives the degree and the leading coefficient. -/
private theorem degree_of_getLast? {o : OrderKind n} {m : MonomialOrder (Fin n)}
    (hm : o.Agrees m) {a : MvPoly n E} (ha : a.Canonical M p o) {e : Exponents n} {c : E}
    (h : a.terms.getLast? = some (e, c)) :
    e.toFinsupp = m.degree (a.interpret M p) ∧
      (M p).interpret c = m.leadingCoeff (a.interpret M p) := by
  have hmem := List.mem_of_getLast? h
  have hsupp : e.toFinsupp ∈ (a.interpret M p).support :=
    (mem_support_interpret_iff M p ha _).2 ⟨_, hmem, rfl⟩
  have hle : ∀ s ∈ (a.interpret M p).support, m.toSyn s ≤ m.toSyn e.toFinsupp := by
    intro s hs
    obtain ⟨x, hx, rfl⟩ := (mem_support_interpret_iff M p ha s).1 hs
    rcases le_of_getLast? ha h x hx with he | hlt
    · rw [he]
    · exact ((hm _ _).2 hlt).le
  have hd : m.degree (a.interpret M p) = e.toFinsupp :=
    m.toSyn.injective (le_antisymm (m.degree_le_iff.2 hle) (m.le_degree hsupp))
  refine ⟨hd.symm, ?_⟩
  rw [MonomialOrder.leadingCoeff, hd, coeff_interpret_of_mem M p ha hmem]

/-- The largest total degree of the monomials of a canonical polynomial is the total degree. -/
private theorem totalDegree_eq {o : OrderKind n} {a : MvPoly n E} (ha : a.Canonical M p o)
    (hA : a.interpret M p ≠ 0) : a.totalDegree = some (a.interpret M p).totalDegree := by
  rw [MvPoly.totalDegree, List.max?_eq_some_iff]
  obtain ⟨s, hs, hsup⟩ :=
    Finset.exists_mem_eq_sup _ (support_nonempty.2 hA) fun s : Fin n →₀ ℕ =>
      s.sum fun _ k => k
  obtain ⟨x, hx, rfl⟩ := (mem_support_interpret_iff M p ha s).1 hs
  refine ⟨List.mem_map.2 ⟨x.1, List.mem_map.2 ⟨x, hx, rfl⟩, ?_⟩, ?_⟩
  · rw [totalDegree, hsup, sum_toFinsupp]
  · simp only [MvPoly.monomials, List.map_map, List.mem_map]
    rintro _ ⟨y, hy, rfl⟩
    rw [Function.comp_apply, ← sum_toFinsupp]
    exact le_totalDegree ((mem_support_interpret_iff M p ha _).2 ⟨y, hy, rfl⟩)

/-- Proves `LeadingTermsAreThoseOfMathlib`. -/
public theorem leadingTermsAreThoseOfMathlib : LeadingTermsAreThoseOfMathlib := by
  intro P E K _ R M hR n r m hm a ha
  dsimp only [MultivariateRing.model] at ha ⊢
  have hzero := interpret_eq_zero_iff M r.coefficients ha
  refine ⟨?_, ?_, fun e c h => degree_of_getLast? hm ha h, totalDegree_eq ha, ?_⟩
  · simp [hzero, MvPoly.leadingTerm]
  · simp [hzero, MvPoly.totalDegree, MvPoly.monomials]
  cases h : a.terms.getLast? with
  | none =>
    refine ⟨false, by simp [MvPoly.isMonic, MvPoly.leadingCoefficient, MvPoly.leadingTerm, h],
      ?_⟩
    simp [hzero, List.getLast?_eq_none_iff.1 h]
  | some t =>
    obtain ⟨e, c⟩ := t
    have hc := ((canonical_iff_terms M _ _ a).1 ha).2 _ (List.mem_of_getLast? h)
    obtain ⟨d, hd, hdc, hdi⟩ := hR.1.subtract _ c _ hc.1 (hR.1.one _).1
    rw [(hR.1.one _).2] at hdi
    have hA : a.interpret M r.coefficients ≠ 0 := fun h0 => by simp [hzero.1 h0] at h
    have hlc := (degree_of_getLast? hm ha h).2
    by_cases h1 : (M r.coefficients).interpret c = 1
    · refine ⟨true, ?_, by simp [hA, MonomialOrder.Monic, ← hlc, h1]⟩
      simp [MvPoly.isMonic, MvPoly.leadingCoefficient, MvPoly.leadingTerm, h, hd,
        testZero_of_eq_zero _ hR.2 hdc (by rw [hdi, h1, sub_self])]
    · refine ⟨false, ?_, by simp [MonomialOrder.Monic, ← hlc, h1]⟩
      simp [MvPoly.isMonic, MvPoly.leadingCoefficient, MvPoly.leadingTerm, h, hd,
        testZero_of_ne_zero _ hR.2 hdc (by rw [hdi]; exact sub_ne_zero.2 h1)]

/-- Proves `NormalizationGivesCanonicalForms`. -/
public theorem normalizationGivesCanonicalForms : NormalizationGivesCanonicalForms := by
  intro P E K _ R M hR n r ts hts
  exact ⟨normalize_yields hR r hts, fun _ h => normalize_perm hR r hts h⟩

end Kalyx.Proofs.Multivariate
