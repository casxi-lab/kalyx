module

public import Kalyx.Proofs.Polynomials.Checks

/-!
# Evaluation at an element

An unregistered helper module of the proofs about the univariate polynomials;
it proves no registered statement. Over a coefficient ring whose ring laws
hold under an interpretation, whatever its zero test:

* the power of a canonical element by repeated squaring is a canonical
  element that denotes the power (`elementPower_spec`), by induction over the
  binary digits of the exponent;
* the value of a canonical polynomial at a canonical element is a canonical
  element that denotes Mathlib's `eval` of the interpretations
  (`eval_spec`), by induction over the terms in their stored order.
-/

namespace Kalyx.Proofs.Polynomials.Evaluation

open Kalyx.Spec.Fields Kalyx.Spec.Polynomials Kalyx.Statements.Polynomials Polynomial
open Kalyx.Proofs.Polynomials.Canonical Kalyx.Proofs.Polynomials.Checks

variable {P E U : Type} {K : P → Type} [∀ p, CommRing (K p)] {R : CoefficientRing P E U}
  {M : Model P E K} {p : P}

/-- The power of a canonical element is a canonical element that denotes the
power. -/
public theorem elementPower_spec (hR : RingLaws R M) {c : E} (hc : (M p).canonical c) (k : ℕ) :
    YieldsElement M p (elementPower R p c k) ((M p).interpret c ^ k) := by
  unfold YieldsElement elementPower
  refine foldlM_binaryDigits
    (fun s j => (M p).canonical s ∧ (M p).interpret s = (M p).interpret c ^ j) _
    (fun s j b ⟨hs, hsj⟩ => ?_) k ⟨(hR.one p).1, by rw [(hR.one p).2, pow_zero]⟩
  obtain ⟨s₁, h₁, hs₁, hs₁i⟩ := hR.multiply p s s hs hs
  cases b with
  | false =>
    refine ⟨s₁, ?_, hs₁, ?_⟩
    · simp only [bind_eq_bind, h₁, ofOutcome_value, bind_value, Bool.false_eq_true, ↓reduceIte,
        pure_eq_value]
    · rw [hs₁i, hsj, ← pow_add, Bool.toNat_false, add_zero, two_mul]
  | true =>
    obtain ⟨s₂, h₂, hs₂, hs₂i⟩ := hR.multiply p s₁ c hs₁ hc
    refine ⟨s₂, ?_, hs₂, ?_⟩
    · simp only [bind_eq_bind, h₁, ofOutcome_value, bind_value, ↓reduceIte, h₂]
    · rw [hs₂i, hs₁i, hsj, ← pow_add, ← pow_succ, Bool.toNat_true, two_mul]

/-- A loop over a list from a canonical element whose every step adds `g` of
the term to a canonical accumulator: a canonical element that denotes the
accumulator plus the sum of `g` over the list. -/
private theorem foldlM_add (f : E → ℕ × E → PolyResult E) (g : ℕ × E → K p)
    (hf : ∀ acc x, (M p).canonical acc → (M p).canonical x.2 →
      YieldsElement M p (f acc x) ((M p).interpret acc + g x)) :
    ∀ (l : List (ℕ × E)) (acc : E) (y : K p), (M p).canonical acc →
      (∀ x ∈ l, (M p).canonical x.2) → y = (M p).interpret acc + (l.map g).sum →
      YieldsElement M p (l.foldlM f acc) y := by
  intro l
  induction l with
  | nil => exact fun acc y hacc _ hy => ⟨acc, rfl, hacc, by simp [hy]⟩
  | cons x l ih =>
    intro acc y hacc hl hy
    obtain ⟨s, hs, hsc, hsi⟩ := hf acc x hacc (hl x List.mem_cons_self)
    rw [List.foldlM_cons, bind_eq_bind, hs, bind_value]
    refine ih s y hsc (fun z hz => hl z (List.mem_cons_of_mem _ hz)) ?_
    rw [hy, hsi, List.map_cons, List.sum_cons, add_assoc]

/-- The value of a canonical polynomial at a canonical element is a canonical
element that denotes Mathlib's `eval` of the interpretations. -/
public theorem eval_spec (hR : RingLaws R M) {a : Poly E} (ha : a.Canonical M p) {c : E}
    (hc : (M p).canonical c) :
    YieldsElement M p (Poly.eval R p a c) ((a.interpret M p).eval ((M p).interpret c)) := by
  unfold Poly.eval
  refine foldlM_add _ (fun x => (M p).interpret x.2 * (M p).interpret c ^ x.1)
    (fun acc x hacc hx => ?_) a.terms (R.zero p) _ (hR.zero p).1
    (fun x hx => (((canonical_iff M p a).1 ha).2 x hx).1) ?_
  · obtain ⟨d, e⟩ := x
    obtain ⟨w, hw, hwc, hwi⟩ := elementPower_spec hR hc d
    obtain ⟨m, hm, hmc, hmi⟩ := hR.multiply p e w hx hwc
    obtain ⟨s, hs, hsc, hsi⟩ := hR.add p acc m hacc hmc
    refine ⟨s, ?_, hsc, by rw [hsi, hmi, hwi]⟩
    simp only [bind_eq_bind, hw, bind_value, hm, ofOutcome_value, hs]
  · rw [(hR.zero p).2, zero_add, Poly.interpret, eval_listSum, List.map_map]
    congr 1
    refine List.map_congr_left fun x _ => ?_
    simp [eval_monomial]

end Kalyx.Proofs.Polynomials.Evaluation
