module

public import Kalyx.Proofs.Polynomials.Checks
public import Kalyx.Proofs.Fields
public import Kalyx.Proofs.Terms.Basics

/-!
# The expansion of terms and its meaning

An unregistered helper module of the proofs about the univariate polynomials;
it proves no registered statement. It holds:

* the rationals as an exact coefficient ring (`rationalRing_exact`), the
  fractions of rationals (`ofRat_reduced`, `ofRat_interpret`) and the
  uniqueness of reduced fractions (`ofRat_interpret_of_reduced`);
* the meaning of the expansion: when the expansion of any term under any
  limits returns a polynomial, the polynomial is canonical and the term is
  defined at every assignment with its value (`expand_denote`), by induction
  over the term, the factors of a product and the monomials of a sum, since
  every operation of the ring that returns a value returns a canonical
  polynomial that denotes its result.
-/

namespace Kalyx.Proofs.Polynomials.Expansion

open Kalyx.Spec.Fields Kalyx.Spec.Polynomials Kalyx.Statements.Polynomials Polynomial
open Kalyx.Spec.Terms (Term Interp zpowMeaning)
open Kalyx.Proofs.Polynomials.Canonical Kalyx.Proofs.Polynomials.Checks

/-! ## The rationals -/

/-- The fraction of a rational number is reduced. -/
public theorem ofRat_reduced (q : ℚ) : (Fraction.ofRat q).Reduced := by
  refine ⟨Int.natCast_pos.mpr q.pos, ?_⟩
  show Nat.gcd q.num.natAbs (q.den : ℤ).natAbs = 1
  rw [Int.natAbs_natCast]
  exact q.reduced

/-- The fraction of a rational number denotes it. -/
@[simp] public theorem ofRat_interpret (q : ℚ) : (Fraction.ofRat q).interpret = q := by
  simp [Fraction.ofRat, Fraction.interpret, Rat.num_div_den]

/-- A reduced fraction is the fraction of the number that it denotes. -/
public theorem ofRat_interpret_of_reduced {f : Fraction} (h : f.Reduced) :
    Fraction.ofRat f.interpret = f := by
  obtain ⟨num, den⟩ := f
  obtain ⟨hd, hg⟩ := h
  have hc : Nat.Coprime num.natAbs den.natAbs := hg
  simp only [Fraction.ofRat, Fraction.interpret, Fraction.mk.injEq]
  exact ⟨Rat.num_div_eq_of_coprime hd hc, Rat.den_div_eq_of_coprime hd hc⟩

/-- The rationals are an exact coefficient ring. -/
public theorem rationalRing_exact : ExactRing rationalRing Rationals.model :=
  ⟨Kalyx.Proofs.Fields.ringAxioms.1, Kalyx.Proofs.Fields.zeroTestsAreExact.1⟩

/-- A result within the limits that is a value is a canonical polynomial that
denotes the expected polynomial. -/
public theorem of_ywl {P E : Type} {K : P → Type} [∀ p, CommRing (K p)] {M : Model P E K}
    {p : P} {o : PolyResult (Poly E)} {x : Polynomial (K p)} {a : Poly E}
    (h : YieldsWithinLimits M p o x) (ho : o = .value a) :
    a.Canonical M p ∧ a.interpret M p = x := by
  rcases h with ⟨b, hb, hbc, hbx⟩ | h | h | h <;> rw [ho] at * <;> try cases h
  cases hb
  exact ⟨hbc, hbx⟩

/-! ## The meaning of the expansion -/

section Expand

variable (L : Limits) (r : PolynomialRing Rationals) (I : Interp)

/-- A node expands into a canonical polynomial with its value at every
assignment, whenever its expansion returns one. -/
private abbrev Expands (t : Term) : Prop :=
  ∀ a, r.expandNode L t = .value a → a.Canonical Rationals.model r.coefficients ∧
    ∀ ρ, t.denote I ρ = some (polyValue r a ρ)

/-- The value of a polynomial whose interpretation is known. -/
private theorem polyValue_of {a : Poly Fraction} {A : Polynomial ℚ}
    (h : a.interpret Rationals.model r.coefficients = A) (ρ : Kalyx.Spec.Terms.Assignment) :
    polyValue r a ρ = A.eval₂ (Rat.castHom ℂ) (ρ r.variableName) := by
  rw [polyValue, h]

/-- The factors of a product, multiplied into a canonical total. -/
private theorem expandFactors_spec :
    ∀ (fs : List Term) (total a : Poly Fraction), (∀ f ∈ fs, Expands L r I f) →
      total.Canonical Rationals.model r.coefficients →
      PolynomialRing.expandFactors L r total fs = .value a →
      a.Canonical Rationals.model r.coefficients ∧ ∀ ρ, ∃ vs,
        Term.denoteList I ρ fs = some vs ∧ polyValue r a ρ = polyValue r total ρ * vs.prod := by
  intro fs
  induction fs with
  | nil =>
    intro total a _ htc h
    simp only [PolynomialRing.expandFactors, PolyResult.value.injEq] at h
    subst h
    exact ⟨htc, fun ρ => ⟨[], by simp [Term.denoteList]⟩⟩
  | cons f fs ih =>
    intro total a hfs htc h
    simp only [PolynomialRing.expandFactors, bind_eq_bind] at h
    obtain ⟨g, hg, h⟩ := bind_eq_value.1 h
    obtain ⟨t, ht, h⟩ := bind_eq_value.1 h
    obtain ⟨hgc, hgd⟩ := hfs f List.mem_cons_self g hg
    obtain ⟨htc', hti⟩ := of_ywl (multiply_ywl rationalRing_exact L r htc hgc) ht
    obtain ⟨hac, had⟩ := ih t a (fun f' hf' => hfs f' (List.mem_cons_of_mem _ hf')) htc' h
    refine ⟨hac, fun ρ => ?_⟩
    obtain ⟨vs, hvs, hav⟩ := had ρ
    refine ⟨polyValue r g ρ :: vs, by simp [Term.denoteList, hgd ρ, hvs], ?_⟩
    rw [hav, polyValue_of r hti, eval₂_mul, ← polyValue, ← polyValue, List.prod_cons, mul_assoc]

/-- The monomials of a sum, each scaled and added to a canonical total. -/
private theorem expandMonomials_spec :
    ∀ (ms : List (ℚ × Term)) (total a : Poly Fraction), (∀ m ∈ ms, Expands L r I m.2) →
      total.Canonical Rationals.model r.coefficients →
      PolynomialRing.expandMonomials L r total ms = .value a →
      a.Canonical Rationals.model r.coefficients ∧ ∀ ρ, ∃ v,
        Term.denotePairs I ρ ms = some v ∧ polyValue r a ρ = polyValue r total ρ + v := by
  intro ms
  induction ms with
  | nil =>
    intro total a _ htc h
    simp only [PolynomialRing.expandMonomials, PolyResult.value.injEq] at h
    subst h
    exact ⟨htc, fun ρ => ⟨0, by simp [Term.denotePairs]⟩⟩
  | cons m ms ih =>
    intro total a hms htc h
    obtain ⟨q, t⟩ := m
    simp only [PolynomialRing.expandMonomials, bind_eq_bind] at h
    obtain ⟨g, hg, h⟩ := bind_eq_value.1 h
    obtain ⟨c, hc, h⟩ := bind_eq_value.1 h
    obtain ⟨s, hs, h⟩ := bind_eq_value.1 h
    obtain ⟨t', ht', h⟩ := bind_eq_value.1 h
    obtain ⟨hgc, hgd⟩ := hms (q, t) List.mem_cons_self g hg
    obtain ⟨hcc, hci⟩ := of_ywl (constant_ywl rationalRing_exact L r (ofRat_reduced q)) hc
    obtain ⟨hsc, hsi⟩ := of_ywl (multiply_ywl rationalRing_exact L r hgc hcc) hs
    obtain ⟨ht'c, ht'i⟩ := of_ywl (add_ywl rationalRing_exact L r htc hsc) ht'
    obtain ⟨hac, had⟩ := ih t' a (fun m' hm' => hms m' (List.mem_cons_of_mem _ hm')) ht'c h
    refine ⟨hac, fun ρ => ?_⟩
    obtain ⟨v, hv, hav⟩ := had ρ
    refine ⟨q * polyValue r g ρ + v, by simp [Term.denotePairs, hgd ρ, hv], ?_⟩
    rw [hav, polyValue_of r ht'i, hsi, hci, eval₂_add, eval₂_mul, eval₂_C]
    simp only [polyValue, Rationals.model, ofRat_interpret, eq_ratCast]
    ring

/-- Every node expands into a canonical polynomial with its value. -/
private theorem expandNode_spec : ∀ t, Expands L r I t := by
  refine Kalyx.Proofs.Terms.term_induct (fun q => ?_) (fun c => ?_) (fun s => ?_)
    (fun h args _ => ?_) (fun b k ih => ?_) (fun c fs ih => ?_) (fun c ms ih => ?_)
    (fun s ops _ => ?_)
  · intro a h
    simp only [PolynomialRing.expandNode] at h
    obtain ⟨hac, hai⟩ := of_ywl (constant_ywl rationalRing_exact L r (ofRat_reduced q)) h
    refine ⟨hac, fun ρ => ?_⟩
    rw [polyValue_of r hai]
    simp [Term.denote, Rationals.model]
  · intro a h
    simp [PolynomialRing.expandNode] at h
  · intro a h
    simp only [PolynomialRing.expandNode] at h
    split at h
    · rename_i hs
      obtain ⟨hac, hai⟩ := of_ywl (generator_ywl rationalRing_exact L r) h
      refine ⟨hac, fun ρ => ?_⟩
      rw [polyValue_of r hai, eval₂_X, hs]
      simp [Term.denote]
    · cases h
  · intro a h'
    simp [PolynomialRing.expandNode] at h'
  · intro a h
    simp only [PolynomialRing.expandNode, bind_eq_bind] at h
    obtain ⟨g, hg, h⟩ := bind_eq_value.1 h
    split at h
    · cases h
    · rename_i hk
      obtain ⟨hgc, hgd⟩ := ih g hg
      obtain ⟨hac, hai⟩ := of_ywl (power_ywl rationalRing_exact L r hgc k.toNat) h
      refine ⟨hac, fun ρ => ?_⟩
      have hk' : k = (k.toNat : ℤ) := (Int.toNat_of_nonneg (not_lt.1 hk)).symm
      rw [polyValue_of r hai, eval₂_pow, ← polyValue]
      simp only [Term.denote, hgd ρ, Option.bind_some, zpowMeaning, hk, and_false,
        ↓reduceIte]
      rw [hk', zpow_natCast, Int.toNat_natCast]
  · intro a h
    simp only [PolynomialRing.expandNode, bind_eq_bind] at h
    obtain ⟨t, ht, h⟩ := bind_eq_value.1 h
    obtain ⟨htc, hti⟩ := of_ywl (constant_ywl rationalRing_exact L r (ofRat_reduced c)) ht
    obtain ⟨hac, had⟩ := expandFactors_spec L r I fs t a ih htc h
    refine ⟨hac, fun ρ => ?_⟩
    obtain ⟨vs, hvs, hav⟩ := had ρ
    rw [hav, polyValue_of r hti]
    simp [Term.denote, hvs, Rationals.model]
  · intro a h
    simp only [PolynomialRing.expandNode, bind_eq_bind] at h
    obtain ⟨t, ht, h⟩ := bind_eq_value.1 h
    obtain ⟨htc, hti⟩ := of_ywl (constant_ywl rationalRing_exact L r (ofRat_reduced c)) ht
    obtain ⟨hac, had⟩ := expandMonomials_spec L r I ms t a ih htc h
    refine ⟨hac, fun ρ => ?_⟩
    obtain ⟨v, hv, hav⟩ := had ρ
    rw [hav, polyValue_of r hti]
    simp [Term.denote, hv, Rationals.model]
  · intro a h
    simp [PolynomialRing.expandNode] at h

end Expand

/-- When the expansion of a term returns a polynomial, the polynomial is
canonical, and the term is defined at every assignment, under every
interpretation, with the value of the polynomial. -/
public theorem expand_denote {L : Limits} {r : PolynomialRing Rationals} {t : Term}
    {a : Poly Fraction} (h : r.expand L t = .value a) (I : Interp) :
    a.Canonical Rationals.model r.coefficients ∧ ∀ ρ, t.denote I ρ = some (polyValue r a ρ) := by
  unfold PolynomialRing.expand at h
  split at h
  · cases h
  · exact expandNode_spec L r I t a h

end Kalyx.Proofs.Polynomials.Expansion
