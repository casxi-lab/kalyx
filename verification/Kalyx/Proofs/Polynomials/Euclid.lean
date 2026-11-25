module

public import Kalyx.Proofs.Polynomials.Remainders

/-!
# The Euclidean algorithms

An unregistered helper module of the proofs about the univariate polynomials;
it proves no registered statement. Over a coefficient field that is exact
under an interpretation in fields (`ExactField`), on canonical operands:

* in Mathlib, a monic GCD is unique (`monicGcdOf_unique`), the monic form of a
  polynomial whose divisors are the common divisors of `A` and `B` is a monic
  GCD (`monicGcdOf_of_dvd_iff`), and `A` and `B` are coprime exactly when
  their monic GCD is `1` (`isRelPrime_iff`);
* the Euclidean algorithm keeps the common divisors of its two remainders
  and ends within its fuel, since each remainder lowers the degree, so the
  monic GCD is canonical and a monic GCD of the interpretations
  (`monicGcd_spec`);
* the extended Euclidean algorithm keeps, besides the common divisors, the
  identity `s A + t B = r` of each state and bounds on the degrees of the
  cofactors of two consecutive states; so its last state, scaled to the monic
  GCD, has the cofactors of lowest degree, which the identity and these
  conditions determine (`extendedGcd_spec`).
-/

namespace Kalyx.Proofs.Polynomials.Euclid

open Kalyx.Spec.Fields Kalyx.Spec.Polynomials Kalyx.Statements.Polynomials Polynomial
open Kalyx.Proofs.Polynomials.Canonical Kalyx.Proofs.Polynomials.Operations
open Kalyx.Proofs.Polynomials.Remainders

/-! ## Monic GCDs in Mathlib -/

section Mathlib

variable {K : Type} [Field K]

/-- A monic GCD of `A` and `B` is unique. -/
public theorem monicGcdOf_unique {A B G G' : K[X]} (h : MonicGcdOf A B G)
    (h' : MonicGcdOf A B G') : G = G' := by
  obtain ⟨hz, hm, hA, hB, hD⟩ := h
  obtain ⟨hz', hm', hA', hB', hD'⟩ := h'
  by_cases h0 : A = 0 ∧ B = 0
  · rw [hz h0, hz' h0]
  · have h0' : A ≠ 0 ∨ B ≠ 0 := by tauto
    exact eq_of_monic_of_associated (hm h0') (hm' h0')
      (associated_of_dvd_dvd (hD' G hA hB) (hD G' hA' hB'))

/-- The monic form of a polynomial whose divisors are the common divisors of
`A` and `B` is a monic GCD of `A` and `B`. -/
public theorem monicGcdOf_of_dvd_iff {A B G : K[X]} (h : ∀ D, D ∣ G ↔ D ∣ A ∧ D ∣ B) :
    MonicGcdOf A B (G * C G.leadingCoeff⁻¹) := by
  by_cases hG : G = 0
  · obtain ⟨hA, hB⟩ := (h 0).1 (by rw [hG])
    rw [zero_dvd_iff] at hA hB
    subst hG hA hB
    simp [MonicGcdOf]
  · have hu : IsUnit (C G.leadingCoeff⁻¹) :=
      isUnit_C.2 (inv_ne_zero (leadingCoeff_ne_zero.2 hG)).isUnit
    obtain ⟨hA, hB⟩ := (h G).1 dvd_rfl
    refine ⟨fun ⟨hA0, hB0⟩ => absurd (zero_dvd_iff.1 ((h 0).2 ⟨by rw [hA0], by rw [hB0]⟩)) hG,
      fun _ => monic_mul_leadingCoeff_inv hG, hu.mul_right_dvd.2 hA, hu.mul_right_dvd.2 hB,
      fun D hDA hDB => hu.dvd_mul_right.2 ((h D).2 ⟨hDA, hDB⟩)⟩

/-- `A` and `B` are coprime exactly when their monic GCD is one. -/
public theorem isRelPrime_iff {A B G : K[X]} (h : MonicGcdOf A B G) :
    IsRelPrime A B ↔ G = 1 := by
  obtain ⟨-, hm, hA, hB, hD⟩ := h
  constructor
  · intro hrel
    by_cases h0 : A = 0 ∧ B = 0
    · obtain ⟨rfl, rfl⟩ := h0
      exact absurd (hrel (dvd_refl 0) (dvd_refl 0)) not_isUnit_zero
    · exact (hm (by tauto)).eq_one_of_isUnit (hrel hA hB)
  · intro hG D hDA hDB
    exact isUnit_of_dvd_one (hG ▸ hD D hDA hDB)

/-! ### Degrees along the extended Euclidean algorithm -/

/-- A step `xr = q yr + r` with `deg r < deg yr`: `deg q + deg yr` and
`deg r` are at most `deg xr`. -/
private theorem step_degrees {xr yr q r : K[X]} (hx : xr = q * yr + r)
    (hr : r.degree < yr.degree) : q.degree + yr.degree ≤ xr.degree ∧ r.degree ≤ xr.degree := by
  by_cases hq : q = 0
  · subst hq
    simp only [zero_mul, zero_add] at hx
    subst hx
    simp
  · have hle : yr.degree ≤ q.degree + yr.degree := le_add_of_nonneg_left (zero_le_degree_iff.2 hq)
    have hlt : r.degree < (q * yr).degree := by
      rw [degree_mul]
      exact lt_of_lt_of_le hr hle
    have hxd : xr.degree = q.degree + yr.degree := by
      rw [hx, degree_add_eq_left_of_degree_lt hlt, degree_mul]
    rw [hxd]
    exact ⟨le_rfl, le_trans hr.le hle⟩

/-- The bounds on the degrees of the cofactors of two consecutive states
`(xs, xt, xr)` and `(ys, yt, yr)` of the extended Euclidean algorithm on `A`
and `B`. -/
private def Bounds (A B xs xt xr ys yt yr : K[X]) : Prop :=
  xs.degree + yr.degree ≤ B.degree ∧ ys.degree + xr.degree ≤ B.degree ∧
    xt.degree + yr.degree ≤ A.degree ∧ yt.degree + xr.degree ≤ A.degree

/-- The conditions on a state `(s, t, r)` that make its cofactors those of
lowest degree once it is the last state with a nonzero remainder. -/
private def Strict (A B s t r : K[X]) : Prop :=
  r = 0 ∨ (s = 0 ∧ r.degree = B.degree) ∨
    (r.degree < B.degree ∧ (s = 0 ∨ s.degree + r.degree < B.degree) ∧
      (t = 0 ∨ t.degree + r.degree < A.degree))

/-- A step of the extended Euclidean algorithm keeps the bounds. -/
private theorem bounds_step {A B xs xt xr ys yt yr q r : K[X]} (hx : xr = q * yr + r)
    (hr : r.degree < yr.degree) (h : Bounds A B xs xt xr ys yt yr) :
    Bounds A B ys yt yr (xs - q * ys) (xt - q * yt) r := by
  obtain ⟨hq, hrx⟩ := step_degrees hx hr
  obtain ⟨h1, h2, h3, h4⟩ := h
  have key : ∀ {X xs ys : K[X]}, xs.degree + yr.degree ≤ X.degree →
      ys.degree + xr.degree ≤ X.degree → (xs - q * ys).degree + yr.degree ≤ X.degree := by
    intro X xs ys h1 h2
    refine le_trans (add_le_add (degree_sub_le _ _) le_rfl) ?_
    rw [← max_add_add_right]
    refine max_le h1 ?_
    rw [degree_mul, add_comm q.degree, add_assoc]
    exact le_trans (add_le_add le_rfl hq) h2
  exact ⟨le_trans (add_le_add le_rfl hrx) h2, key h1 h2, le_trans (add_le_add le_rfl hrx) h4,
    key h3 h4⟩

/-- A state whose remainder lies below that of the state before it, with the
bounds of the two, meets the conditions of `Strict`. -/
private theorem strict_of_bounds {A B s t r r' : K[X]} (hB : r'.degree ≤ B.degree)
    (hr : r.degree < r'.degree) (hs : s.degree + r'.degree ≤ B.degree)
    (ht : t.degree + r'.degree ≤ A.degree) : Strict A B s t r := by
  by_cases h0 : r = 0
  · exact Or.inl h0
  refine Or.inr (Or.inr ⟨lt_of_lt_of_le hr hB, ?_, ?_⟩)
  · by_cases hs0 : s = 0
    · exact Or.inl hs0
    · exact Or.inr (lt_of_lt_of_le (WithBot.add_lt_add_left (degree_ne_bot.2 hs0) hr) hs)
  · by_cases ht0 : t = 0
    · exact Or.inl ht0
    · exact Or.inr (lt_of_lt_of_le (WithBot.add_lt_add_left (degree_ne_bot.2 ht0) hr) ht)

/-- The remainder of a state with the conditions of `Strict` lies at or below
the degree of `B`. -/
private theorem Strict.degree_le {A B s t r : K[X]} (h : Strict A B s t r) :
    r.degree ≤ B.degree := by
  rcases h with h | ⟨-, h⟩ | ⟨h, -⟩
  · rw [h, degree_zero]
    exact bot_le
  · exact h.le
  · exact h.le

/-! ### The cofactors of lowest degree -/

/-- The conditions of `Poly.lowestCofactors` on the interpretations. -/
private def Lowest (A B S T G : K[X]) : Prop :=
  (B = 0 → T = 0 ∧ (A = 0 → S = 0)) ∧
    (B ≠ 0 → G ≠ 0 ∧ (G.degree = B.degree → S = 0) ∧
      (G.degree ≠ B.degree → G.degree = A.degree → T = 0) ∧
      (G.degree ≠ B.degree → G.degree ≠ A.degree →
        (S = 0 ∨ S.degree + G.degree < B.degree) ∧ (T = 0 ∨ T.degree + G.degree < A.degree)))

/-- The last state of the extended Euclidean algorithm, with a nonzero
remainder whose divisors are the common divisors of `A` and `B`, scaled by a
nonzero constant: its cofactors meet the conditions of lowest degree. -/
private theorem lowest_of_final {A B s t r : K[X]} {k : K} (hk : k ≠ 0) (hr : r ≠ 0)
    (hD : ∀ D, D ∣ r ↔ D ∣ A ∧ D ∣ B) (h : (B = 0 ∧ t = 0) ∨ (B ≠ 0 ∧ Strict A B s t r)) :
    Lowest A B (C k * s) (C k * t) (C k * r) := by
  have hC : ∀ x : K[X], C k * x = 0 ↔ x = 0 := fun x => by simp [hk]
  simp only [Lowest, ne_eq, hC, degree_C_mul hk]
  refine ⟨fun hB => ?_, fun hB => ⟨hr, ?_⟩⟩
  · rcases h with ⟨-, ht⟩ | ⟨hB', -⟩
    · refine ⟨ht, fun hA => absurd ?_ hr⟩
      exact zero_dvd_iff.1 ((hD 0).2 ⟨by rw [hA], by rw [hB]⟩)
    · exact absurd hB hB'
  · rcases h with ⟨hB', -⟩ | ⟨-, h | ⟨hs, hrB⟩ | ⟨hrB, hs, ht⟩⟩
    · exact absurd hB' hB
    · exact absurd h hr
    · exact ⟨fun _ => hs, fun h => absurd hrB h, fun h => absurd hrB h⟩
    · refine ⟨fun h => absurd h hrB.ne, fun _ hA => ?_, fun _ _ => ⟨hs, ht⟩⟩
      rcases ht with ht | ht
      · exact ht
      · by_contra ht0
        rw [← hA] at ht
        exact absurd ht (not_lt.2 (le_add_of_nonneg_left (zero_le_degree_iff.2 ht0)))

/-- Two pairs of cofactors with `S A + T B = G` for a common divisor `G` of
`A` and `B`, both with the conditions of lowest degree, are equal. -/
private theorem lowest_unique {A B S₁ T₁ S₂ T₂ G : K[X]} (hGA : G ∣ A) (hGB : G ∣ B)
    (h₁ : S₁ * A + T₁ * B = G) (h₂ : S₂ * A + T₂ * B = G) (l₁ : Lowest A B S₁ T₁ G)
    (l₂ : Lowest A B S₂ T₂ G) : S₁ = S₂ ∧ T₁ = T₂ := by
  by_cases hB : B = 0
  · obtain ⟨hT₁, hS₁⟩ := l₁.1 hB
    obtain ⟨hT₂, hS₂⟩ := l₂.1 hB
    subst hT₁ hT₂
    refine ⟨?_, rfl⟩
    by_cases hA : A = 0
    · rw [hS₁ hA, hS₂ hA]
    · subst hB
      exact mul_right_cancel₀ hA (by linear_combination h₁ - h₂)
  · obtain ⟨hG, l₁a, l₁b, l₁c⟩ := l₁.2 hB
    obtain ⟨-, l₂a, l₂b, l₂c⟩ := l₂.2 hB
    have hS : S₁ = S₂ := by
      by_cases hGB' : G.degree = B.degree
      · rw [l₁a hGB', l₂a hGB']
      by_cases hGA' : G.degree = A.degree
      · have hA : A ≠ 0 := fun h => hG (by rw [h, degree_zero] at hGA'; exact degree_eq_bot.1 hGA')
        have hT1 := l₁b hGB' hGA'
        have hT2 := l₂b hGB' hGA'
        subst hT1 hT2
        exact mul_right_cancel₀ hA (by linear_combination h₁ - h₂)
      obtain ⟨hs₁, -⟩ := l₁c hGB' hGA'
      obtain ⟨hs₂, -⟩ := l₂c hGB' hGA'
      obtain ⟨A', rfl⟩ := hGA
      obtain ⟨B', rfl⟩ := hGB
      have hB' : B' ≠ 0 := right_ne_zero_of_mul hB
      have hcop : IsCoprime B' A' :=
        ⟨T₁, S₁, mul_left_cancel₀ hG (by linear_combination h₁)⟩
      have hdvd : B' ∣ A' * (S₁ - S₂) :=
        ⟨T₂ - T₁, mul_left_cancel₀ hG (by linear_combination h₁ - h₂)⟩
      have hlt : ∀ S : K[X], (S = 0 ∨ S.degree + G.degree < (G * B').degree) →
          S.degree < B'.degree := by
        intro S hS
        rcases hS with rfl | hS
        · rw [degree_zero]
          exact bot_lt_iff_ne_bot.2 (degree_ne_bot.2 hB')
        · rw [degree_mul, add_comm G.degree] at hS
          exact (WithBot.add_lt_add_iff_right (degree_ne_bot.2 hG)).1 hS
      exact sub_eq_zero.1 (eq_zero_of_dvd_of_degree_lt (hcop.dvd_of_dvd_mul_left hdvd)
        (lt_of_le_of_lt (degree_sub_le _ _) (max_lt (hlt _ hs₁) (hlt _ hs₂))))
    subst hS
    exact ⟨rfl, mul_right_cancel₀ hB (by linear_combination h₁ - h₂)⟩

end Mathlib

variable {P E : Type} {K : P → Type} [∀ p, Field (K p)] {F : CoefficientField P E Empty}
  {M : Model P E K} {p : P}

/-- A degree below one that lies below `f + 1` lies below `f`. -/
private theorem lt_of_lt_of_lt_succ {x y : WithBot ℕ} {f : ℕ} (h : x < y)
    (h' : y < ((f + 1 : ℕ) : WithBot ℕ)) : x < f := by
  induction y using WithBot.recBotCoe with
  | bot => exact absurd h not_lt_bot
  | coe n =>
    rw [Nat.cast_withBot, WithBot.coe_lt_coe] at h'
    refine lt_of_lt_of_le h ?_
    rw [Nat.cast_withBot]
    exact WithBot.coe_le_coe.2 (Nat.lt_succ_iff.1 h')

/-- The common divisors of `xr` and `yr` are those of `yr` and `r` for
`xr = q yr + r`. -/
private theorem dvd_step {L : Type} [CommRing L] {xr yr q r : L} (hx : xr = q * yr + r) (D : L) :
    D ∣ yr ∧ D ∣ r ↔ D ∣ xr ∧ D ∣ yr := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hx ▸ dvd_add (dvd_mul_of_dvd_right h1 _) h2, h1⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    have hr : r = xr - q * yr := by rw [hx]; ring
    rw [hr]
    exact dvd_sub h1 (dvd_mul_of_dvd_right h2 _)

/-! ## The monic GCD -/

/-- The Euclidean algorithm from canonical remainders whose common divisors
are those of `A` and `B`, within its fuel: a canonical polynomial whose
divisors are the common divisors of `A` and `B`. -/
private theorem euclid_spec (hF : ExactField F M) {A B : (K p)[X]} :
    ∀ (fuel : ℕ) (r₀ r₁ : Poly E), r₀.Canonical M p → r₁.Canonical M p →
      (r₁.interpret M p).degree < fuel →
      (∀ D, D ∣ r₀.interpret M p ∧ D ∣ r₁.interpret M p ↔ D ∣ A ∧ D ∣ B) →
      ∃ g, Poly.euclid F p fuel r₀ r₁ = .value g ∧ g.Canonical M p ∧
        ∀ D, D ∣ g.interpret M p ↔ D ∣ A ∧ D ∣ B := by
  intro fuel
  induction fuel with
  | zero =>
    intro r₀ r₁ h₀ h₁ hdeg hD
    have hr₁ : r₁ = Poly.zero := (interpret_eq_zero_iff M p h₁).1
      (degree_eq_bot.1 (Nat.WithBot.lt_zero_iff.1 hdeg))
    subst hr₁
    exact ⟨r₀, rfl, h₀, fun D => by rw [← hD]; simp⟩
  | succ f ih =>
    intro r₀ r₁ h₀ h₁ hdeg hD
    by_cases hz : r₁ = Poly.zero
    · subst hz
      exact ⟨r₀, rfl, h₀, fun D => by rw [← hD]; simp⟩
    · have hz' : r₁.isZero = false := by
        cases h : r₁.isZero
        · rfl
        · exact absurd ((isZero_iff r₁).1 h) hz
      obtain ⟨q, r₂, -, hr₂, -, h₂, hdiv, hd₂⟩ := divRem_spec hF h₀ h₁ hz
      obtain ⟨g, hg, hgc, hgD⟩ := ih r₁ r₂ h₁ h₂ (lt_of_lt_of_lt_succ hd₂ hdeg)
        (fun D => (dvd_step hdiv D).trans (hD D))
      refine ⟨g, ?_, hgc, hgD⟩
      rw [Poly.euclid.eq_2]
      simp only [hz', Bool.false_eq_true, ↓reduceIte, bind_eq_bind, hr₂, bind_value, hg]

/-- The monic GCD of canonical polynomials is canonical and a monic GCD of
their interpretations. -/
public theorem monicGcd_spec (hF : ExactField F M) {a b : Poly E} (ha : a.Canonical M p)
    (hb : b.Canonical M p) :
    ∃ g, Poly.monicGcd F p a b = .value g ∧ g.Canonical M p ∧
      MonicGcdOf (a.interpret M p) (b.interpret M p) (g.interpret M p) := by
  obtain ⟨g₀, hg₀, hg₀c, hg₀D⟩ := euclid_spec hF (A := a.interpret M p)
    (B := b.interpret M p) _ a b ha hb (degree_lt_fuel hb) (fun D => Iff.rfl)
  obtain ⟨g, hg, hgc, hgi⟩ := monicForm_spec hF hg₀c
  refine ⟨g, by simp only [Poly.monicGcd, bind_eq_bind, hg₀, bind_value, hg], hgc, ?_⟩
  rw [hgi]
  exact monicGcdOf_of_dvd_iff hg₀D

/-! ## The extended GCD -/

/-- A state of the extended Euclidean algorithm on `A` and `B`: canonical
polynomials with `s A + t B = r`. -/
private abbrev Good (M : Model P E K) (p : P) (A B : (K p)[X]) (x : Bezout E) : Prop :=
  x.left.Canonical M p ∧ x.right.Canonical M p ∧ x.gcd.Canonical M p ∧
    x.left.interpret M p * A + x.right.interpret M p * B = x.gcd.interpret M p

/-- The extended Euclidean algorithm from two states whose remainders have
the common divisors of `A` and `B`, with the bounds of consecutive states and
the conditions of `Strict` on the second, and on the first when the second
remainder is zero, within its fuel: a last state whose remainder has the
common divisors of `A` and `B` as divisors, with the conditions of
`Strict`. -/
private theorem extendedEuclid_spec (hF : ExactField F M) {A B : (K p)[X]} :
    ∀ (fuel : ℕ) (x y : Bezout E), Good M p A B x → Good M p A B y →
      (∀ D, D ∣ x.gcd.interpret M p ∧ D ∣ y.gcd.interpret M p ↔ D ∣ A ∧ D ∣ B) →
      Bounds A B (x.left.interpret M p) (x.right.interpret M p) (x.gcd.interpret M p)
        (y.left.interpret M p) (y.right.interpret M p) (y.gcd.interpret M p) →
      Strict A B (y.left.interpret M p) (y.right.interpret M p) (y.gcd.interpret M p) →
      (y.gcd = Poly.zero →
        Strict A B (x.left.interpret M p) (x.right.interpret M p) (x.gcd.interpret M p)) →
      (y.gcd.interpret M p).degree < fuel →
      ∃ e, Poly.extendedEuclid F p fuel x y = .value e ∧ Good M p A B e ∧
        (∀ D, D ∣ e.gcd.interpret M p ↔ D ∣ A ∧ D ∣ B) ∧
        Strict A B (e.left.interpret M p) (e.right.interpret M p) (e.gcd.interpret M p) := by
  intro fuel
  induction fuel with
  | zero =>
    intro x y hx hy hD _ _ hsx hdeg
    have hy0 : y.gcd = Poly.zero := (interpret_eq_zero_iff M p hy.2.2.1).1
      (degree_eq_bot.1 (Nat.WithBot.lt_zero_iff.1 hdeg))
    refine ⟨x, ?_, hx, fun D => by rw [← hD, hy0]; simp, hsx hy0⟩
    rw [Poly.extendedEuclid.eq_1, hy0]
    rfl
  | succ f ih =>
    intro x y hx hy hD hb hsy hsx hdeg
    by_cases hy0 : y.gcd = Poly.zero
    · refine ⟨x, ?_, hx, fun D => by rw [← hD, hy0]; simp, hsx hy0⟩
      rw [Poly.extendedEuclid.eq_2, hy0]
      rfl
    · have hyz : y.gcd.isZero = false := by
        cases h : y.gcd.isZero
        · rfl
        · exact absurd ((isZero_iff _).1 h) hy0
      obtain ⟨hxs, hxt, hxr, hxb⟩ := hx
      obtain ⟨hys, hyt, hyr, hyb⟩ := hy
      obtain ⟨q, r, hqr, -, hqc, hrc, hdiv, hrd⟩ := divRem_spec hF hxr hyr hy0
      obtain ⟨u₁, hu₁, hu₁c, hu₁i⟩ := product_spec hF.1 hqc hys
      obtain ⟨s, hs, hsc, hsi⟩ := difference_spec hF.1 hxs hu₁c
      obtain ⟨u₂, hu₂, hu₂c, hu₂i⟩ := product_spec hF.1 hqc hyt
      obtain ⟨t, ht, htc, hti⟩ := difference_spec hF.1 hxt hu₂c
      have hb' := bounds_step hdiv hrd hb
      rw [← hu₁i, ← hsi, ← hu₂i, ← hti] at hb'
      obtain ⟨e, he, heg, heD, hes⟩ := ih y ⟨s, t, r⟩ ⟨hys, hyt, hyr, hyb⟩
        ⟨hsc, htc, hrc, by
          show s.interpret M p * A + t.interpret M p * B = r.interpret M p
          rw [hsi, hti, hu₁i, hu₂i]
          linear_combination hxb - q.interpret M p * hyb + hdiv⟩
        (fun D => (dvd_step hdiv D).trans (hD D)) hb'
        (strict_of_bounds hsy.degree_le hrd hb'.2.1 hb'.2.2.2) (fun _ => hsy)
        (lt_of_lt_of_lt_succ hrd hdeg)
      refine ⟨e, ?_, heg, heD, hes⟩
      rw [Poly.extendedEuclid.eq_2]
      simp only [hyz, Bool.false_eq_true, ↓reduceIte, bind_eq_bind, hqr, bind_value, hu₁, hs,
        hu₂, ht, he]

/-- `isZero` is the absence of a degree. -/
private theorem isZero_eq_isNone (x : Poly E) : x.isZero = x.degree.isNone := by
  obtain ⟨l⟩ := x
  cases l <;> simp [Poly.isZero, Poly.degree]

/-- The conditions of `Poly.lowestCofactors` on canonical polynomials are those
of `Lowest` on their interpretations. -/
private theorem lowestCofactors_iff {a b s t g : Poly E} (ha : a.Canonical M p)
    (hb : b.Canonical M p) (hs : s.Canonical M p) (ht : t.Canonical M p)
    (hg : g.Canonical M p) :
    Poly.lowestCofactors a b s t g = true ↔ Lowest (a.interpret M p) (b.interpret M p)
      (s.interpret M p) (t.interpret M p) (g.interpret M p) := by
  have hz : ∀ {x : Poly E}, x.Canonical M p → (x.interpret M p = 0 ↔ x.degree = none) :=
    fun hx => (interpret_eq_zero_iff M p hx).trans (degree_eq_none_iff _).symm
  unfold Poly.lowestCofactors Lowest
  simp only [ne_eq, hz ha, hz hb, hz hs, hz ht, hz hg, degree_interpret M p ha,
    degree_interpret M p hb, degree_interpret M p hs, degree_interpret M p ht,
    degree_interpret M p hg, isZero_eq_isNone]
  cases a.degree <;> cases b.degree <;> cases s.degree <;> cases t.degree <;> cases g.degree <;>
    simp <;> simp [WithBot.some_eq_coe, WithBot.none_eq_bot, ← WithBot.coe_add] <;> omega

/-- The extended GCD of canonical polynomials: canonical cofactors and the
monic GCD, with `s A + t B = g` and the conditions of the cofactors of lowest
degree, which determine the cofactors among canonical polynomials. -/
public theorem extendedGcd_spec (hF : ExactField F M) {a b : Poly E} (ha : a.Canonical M p)
    (hb : b.Canonical M p) :
    ∃ e : Bezout E, Poly.extendedGcd F p a b = .value e ∧
      e.left.Canonical M p ∧ e.right.Canonical M p ∧ Poly.monicGcd F p a b = .value e.gcd ∧
      e.left.interpret M p * a.interpret M p + e.right.interpret M p * b.interpret M p =
        e.gcd.interpret M p ∧
      Poly.lowestCofactors a b e.left e.right e.gcd = true ∧
      ∀ s t, s.Canonical M p → t.Canonical M p →
        s.interpret M p * a.interpret M p + t.interpret M p * b.interpret M p =
          e.gcd.interpret M p →
        Poly.lowestCofactors a b s t e.gcd = true → s = e.left ∧ t = e.right := by
  have hu := hF.1.1.unique p
  obtain ⟨one, hone, honec, honei⟩ := monomial_spec hF.1.2 0 (hF.1.1.one p).1
  have hone1 : one.interpret M p = 1 := by
    rw [honei, (hF.1.1.one p).2, monomial_zero_left, map_one]
  obtain ⟨g, hg, hgc, hgG⟩ := monicGcd_spec hF ha hb
  obtain ⟨e, he, ⟨hes, het, her, heb⟩, heD, hfin⟩ : ∃ e,
      Poly.extendedEuclid F p (b.degree.getD 0 + 1) ⟨one, Poly.zero, a⟩ ⟨Poly.zero, one, b⟩ =
        .value e ∧ Good M p (a.interpret M p) (b.interpret M p) e ∧
      (∀ D, D ∣ e.gcd.interpret M p ↔ D ∣ a.interpret M p ∧ D ∣ b.interpret M p) ∧
      ((b.interpret M p = 0 ∧ e.right.interpret M p = 0) ∨ (b.interpret M p ≠ 0 ∧
        Strict (a.interpret M p) (b.interpret M p) (e.left.interpret M p)
          (e.right.interpret M p) (e.gcd.interpret M p))) := by
    by_cases hb0 : b = Poly.zero
    · subst hb0
      exact ⟨⟨one, Poly.zero, a⟩, rfl, ⟨honec, canonical_zero M p, ha, by simp [hone1]⟩,
        fun D => by simp, Or.inl ⟨by simp, by simp⟩⟩
    · have hB : b.interpret M p ≠ 0 := fun h => hb0 ((interpret_eq_zero_iff M p hb).1 h)
      obtain ⟨e, he, heg, heD, hes⟩ := extendedEuclid_spec hF _ ⟨one, Poly.zero, a⟩
        ⟨Poly.zero, one, b⟩ ⟨honec, canonical_zero M p, ha, by simp [hone1]⟩
        ⟨canonical_zero M p, honec, hb, by simp [hone1]⟩ (fun D => Iff.rfl)
        (by simp [Bounds, hone1]) (Or.inr (Or.inl ⟨interpret_zero M p, rfl⟩))
        (fun h => absurd h hb0) (degree_lt_fuel hb)
      exact ⟨e, he, heg, heD, Or.inr ⟨hB, hes⟩⟩
  suffices h : ∃ e' : Bezout E, Poly.extendedGcd F p a b = .value e' ∧
      e'.left.Canonical M p ∧ e'.right.Canonical M p ∧ e'.gcd.Canonical M p ∧
      MonicGcdOf (a.interpret M p) (b.interpret M p) (e'.gcd.interpret M p) ∧
      e'.left.interpret M p * a.interpret M p + e'.right.interpret M p * b.interpret M p =
        e'.gcd.interpret M p ∧
      Lowest (a.interpret M p) (b.interpret M p) (e'.left.interpret M p)
        (e'.right.interpret M p) (e'.gcd.interpret M p) by
    obtain ⟨e', he', hs', ht', hg', hG', hbz', hl'⟩ := h
    have hgg : g = e'.gcd := eq_of_interpret_eq M p hu hgc hg' (monicGcdOf_unique hgG hG')
    refine ⟨e', he', hs', ht', by rw [hg, hgg], hbz', (lowestCofactors_iff ha hb hs' ht' hg').2 hl',
      fun s t hs ht hst hl => ?_⟩
    obtain ⟨h1, h2⟩ := lowest_unique hG'.2.2.1 hG'.2.2.2.1 hst hbz'
      ((lowestCofactors_iff ha hb hs ht hg').1 hl) hl'
    exact ⟨eq_of_interpret_eq M p hu hs hs' h1, eq_of_interpret_eq M p hu ht ht' h2⟩
  cases hlc : e.gcd.leadingCoefficient with
  | none =>
    have he0 : e.gcd = Poly.zero := (leadingCoefficient_eq_none_iff _).1 hlc
    obtain ⟨hA0, hB0⟩ : a.interpret M p = 0 ∧ b.interpret M p = 0 := by
      have := (heD 0).1 (by rw [he0, interpret_zero])
      exact ⟨zero_dvd_iff.1 this.1, zero_dvd_iff.1 this.2⟩
    refine ⟨⟨Poly.zero, Poly.zero, Poly.zero⟩, ?_, canonical_zero M p, canonical_zero M p,
      canonical_zero M p, ?_, by simp, ?_⟩
    · simp only [Poly.extendedGcd, hone, bind_eq_bind, bind_value, he, hlc, pure_eq_value]
    · simp [MonicGcdOf, hA0, hB0]
    · simp [Lowest, hA0, hB0]
  | some c =>
    obtain ⟨hcc, hc0⟩ : (M p).canonical c ∧ (M p).interpret c ≠ 0 := by
      obtain ⟨t, ht, rfl⟩ : ∃ t, e.gcd.terms.getLast? = some t ∧ t.2 = c := by
        simpa [Poly.leadingCoefficient] using hlc
      exact ((canonical_iff M p _).1 her).2 _ (List.mem_of_getLast? ht)
    obtain ⟨u, hu', huc, hcu⟩ := hF.2.inverse p c hcc hc0
    obtain ⟨s', hs', hs'c, hs'i⟩ := scale_spec hF.1 huc hes
    obtain ⟨t', ht', ht'c, ht'i⟩ := scale_spec hF.1 huc het
    obtain ⟨g', hg', hg'c, hg'i⟩ := scale_spec hF.1 huc her
    have hui : (M p).interpret u = (e.gcd.interpret M p).leadingCoeff⁻¹ := by
      rw [leadingCoeff_interpret M p her, hlc]
      exact (inv_eq_of_mul_eq_one_right hcu).symm
    have he0 : e.gcd.interpret M p ≠ 0 := by
      intro h
      rw [(interpret_eq_zero_iff M p her).1 h] at hlc
      exact absurd hlc (by simp [Poly.leadingCoefficient, Poly.zero])
    refine ⟨⟨s', t', g'⟩, ?_, hs'c, ht'c, hg'c, ?_, ?_, ?_⟩
    · simp only [Poly.extendedGcd, hone, bind_eq_bind, bind_value, he, hlc, hu', ofOutcome_value,
        hs', ht', hg', pure_eq_value]
    · show MonicGcdOf _ _ (g'.interpret M p)
      rw [hg'i, hui, mul_comm]
      exact monicGcdOf_of_dvd_iff heD
    · show s'.interpret M p * _ + t'.interpret M p * _ = g'.interpret M p
      rw [hs'i, ht'i, hg'i, ← heb]
      ring
    · show Lowest _ _ (s'.interpret M p) (t'.interpret M p) (g'.interpret M p)
      rw [hs'i, ht'i, hg'i]
      exact lowest_of_final (right_ne_zero_of_mul_eq_one hcu) he0 heD hfin

end Kalyx.Proofs.Polynomials.Euclid
