module

public import Kalyx.Proofs.Polynomials.Operations

/-!
# Long division, remainders and the monic form

An unregistered helper module of the proofs about the univariate polynomials;
it proves no registered statement. Over a coefficient field that is exact
under an interpretation in fields (`ExactField`), on canonical operands:

* `A = q B + r` with `deg r < deg B` determines `q` and `r` in Mathlib
  (`divRem_unique`);
* a step of long division cancels the leading term of the working remainder,
  whose degree drops (`divisionStep_spec`), so long division keeps
  `A = q B + w` and ends within its fuel with a remainder below the degree of
  the divisor, which the loop without the quotient reaches too
  (`longDivision_spec`);
* the degree of a canonical polynomial lies below the fuel of the loops
  (`degree_lt_fuel`), so division with remainder returns the canonical
  quotient and remainder, and the remainder alone is that remainder
  (`divRem_spec`, `rem_spec`); both are `DivisionByZero` for the zero divisor
  (`divRem_zero`, `rem_zero`);
* the monic form denotes the polynomial times the inverse of its leading
  coefficient (`monicForm_spec`).
-/

namespace Kalyx.Proofs.Polynomials.Remainders

open Kalyx.Spec.Fields Kalyx.Spec.Polynomials Kalyx.Statements.Polynomials Polynomial
open Kalyx.Proofs.Polynomials.Canonical Kalyx.Proofs.Polynomials.Operations

/-! ## Uniqueness in Mathlib -/

/-- `A = q B + r` with `deg r < deg B` determines the quotient `q` and the
remainder `r`. -/
public theorem divRem_unique {K : Type} [Field K] {A B q r Q R : K[X]} (hB : B ≠ 0)
    (h : A = q * B + r) (hr : r.degree < B.degree) (h' : A = Q * B + R)
    (hR : R.degree < B.degree) : Q = q ∧ R = r := by
  have hdvd : B ∣ R - r := ⟨q - Q, by linear_combination h - h'⟩
  have hdeg : (R - r).degree < B.degree := lt_of_le_of_lt (degree_sub_le _ _) (max_lt hR hr)
  have hRr : R = r := sub_eq_zero.mp (eq_zero_of_dvd_of_degree_lt hdvd hdeg)
  subst hRr
  have h0 : (Q - q) * B = 0 := by linear_combination h - h'
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right hB), rfl⟩

variable {P E : Type} {K : P → Type} [∀ p, Field (K p)] {F : CoefficientField P E Empty}
  {M : Model P E K} {p : P}

/-! ## Long division -/

/-- A step of long division by a canonical `b`, whose last term is `l x^m`,
with the inverse `u` of `l`, on a canonical working remainder whose last term
`c x^d` lies at or above `m`: a canonical quotient term `t` and a canonical
remainder `w - t b` of lower degree. -/
public theorem divisionStep_spec (hF : ExactField F M) {b : Poly E} (hb : b.Canonical M p)
    {m : ℕ} {l u : E} (hl : b.terms.getLast? = some (m, l)) (hu : (M p).canonical u)
    (hlu : (M p).interpret l * (M p).interpret u = 1) {w : Poly E} (hw : w.Canonical M p)
    {d : ℕ} {c : E} (hwl : w.terms.getLast? = some (d, c)) (hmd : m ≤ d) :
    ∃ t w', Poly.divisionStep F.toCoefficientRing p b m u w d c = .value (t, w') ∧
      t.Canonical M p ∧ w'.Canonical M p ∧
      w'.interpret M p = w.interpret M p - t.interpret M p * b.interpret M p ∧
      (w'.interpret M p).degree < d := by
  obtain ⟨hc, hc0⟩ := ((canonical_iff M p w).1 hw).2 _ (List.mem_of_getLast? hwl)
  obtain ⟨k, hk, hkc, hki⟩ := hF.1.1.multiply p c u hc hu
  obtain ⟨t, ht, htc, hti⟩ := monomial_spec hF.1.2 (d - m) hkc
  obtain ⟨v, hv, hvc, hvi⟩ := product_spec hF.1 htc hb
  obtain ⟨w', hw', hw'c, hw'i⟩ := difference_spec hF.1 hw hvc
  refine ⟨t, w', ?_, htc, hw'c, by rw [hw'i, hvi], ?_⟩
  · simp only [Poly.divisionStep, bind_eq_bind, hk, ofOutcome_value, bind_value, ht, hv, hw',
      pure_eq_value]
  · obtain ⟨hwd, -, hwc⟩ := degree_interpret_of_getLast? M p hw hwl
    obtain ⟨hbd, -, hbc⟩ := degree_interpret_of_getLast? M p hb hl
    have hu0 : (M p).interpret u ≠ 0 := right_ne_zero_of_mul_eq_one hlu
    have hk0 : (M p).interpret c * (M p).interpret u ≠ 0 := mul_ne_zero hc0 hu0
    have htb : (t.interpret M p * b.interpret M p).degree = d := by
      rw [degree_mul, hti, hki, degree_monomial _ hk0, hbd]
      norm_cast
      omega
    have htl : (t.interpret M p * b.interpret M p).leadingCoeff = (M p).interpret c := by
      rw [leadingCoeff_mul, hti, hki, leadingCoeff_monomial, hbc, mul_assoc,
        mul_comm ((M p).interpret u), hlu, mul_one]
    have hw0 : w.interpret M p ≠ 0 := by
      intro h0
      rw [h0, degree_zero] at hwd
      exact WithBot.bot_ne_coe hwd
    rw [hw'i, hvi, ← hwd]
    exact degree_sub_lt_left (hwd.trans htb.symm) hw0 (hwc.trans htl.symm)

/-- Long division by a canonical `b`, whose last term is `l x^m`, with the
inverse `u` of `l`, from a canonical quotient and a canonical working
remainder whose degree lies below the fuel: a canonical quotient and a
canonical remainder below `m`, which keep `q b + w`, and the loop without the
quotient reaches the same remainder. -/
public theorem longDivision_spec (hF : ExactField F M) {b : Poly E} (hb : b.Canonical M p)
    {m : ℕ} {l u : E} (hl : b.terms.getLast? = some (m, l)) (hu : (M p).canonical u)
    (hlu : (M p).interpret l * (M p).interpret u = 1) :
    ∀ (fuel : ℕ) (q w : Poly E), q.Canonical M p → w.Canonical M p →
      (w.interpret M p).degree < fuel →
      ∃ q' r, Poly.longDivision F.toCoefficientRing p b m u fuel q w = .value (q', r) ∧
        Poly.remainderSteps F.toCoefficientRing p b m u fuel w = .value r ∧
        q'.Canonical M p ∧ r.Canonical M p ∧
        q.interpret M p * b.interpret M p + w.interpret M p =
          q'.interpret M p * b.interpret M p + r.interpret M p ∧
        (r.interpret M p).degree < m := by
  intro fuel
  induction fuel with
  | zero =>
    intro q w hq hw hdeg
    cases hwl : w.terms.getLast? with
    | none =>
      have hw0 : w = Poly.zero := (degree_eq_none_iff w).1 (by simp [Poly.degree, hwl])
      subst hw0
      exact ⟨q, Poly.zero, rfl, rfl, hq, hw, rfl, by simp⟩
    | some t =>
      obtain ⟨d, c⟩ := t
      rw [(degree_interpret_of_getLast? M p hw hwl).1] at hdeg
      exact absurd hdeg (by simp)
  | succ f ih =>
    intro q w hq hw hdeg
    cases hwl : w.terms.getLast? with
    | none =>
      have hw0 : w = Poly.zero := (degree_eq_none_iff w).1 (by simp [Poly.degree, hwl])
      subst hw0
      exact ⟨q, Poly.zero, rfl, rfl, hq, hw, rfl, by simp⟩
    | some t =>
      obtain ⟨d, c⟩ := t
      have hwd := (degree_interpret_of_getLast? M p hw hwl).1
      by_cases hmd : m ≤ d
      · obtain ⟨t, w', hst, htc, hw'c, hw'i, hw'd⟩ := divisionStep_spec hF hb hl hu hlu hw hwl hmd
        obtain ⟨q₁, hq₁, hq₁c, hq₁i⟩ := sum_spec hF.1 hq htc
        have hdf : d ≤ f := by
          rw [hwd] at hdeg
          exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast hdeg)
        have hdeg' : (w'.interpret M p).degree < f :=
          lt_of_lt_of_le hw'd (by exact_mod_cast hdf)
        obtain ⟨q', r, h1, h2, hq'c, hrc, hi, hrd⟩ := ih q₁ w' hq₁c hw'c hdeg'
        refine ⟨q', r, ?_, ?_, hq'c, hrc, ?_, hrd⟩
        · rw [Poly.longDivision.eq_1]
          simp only [hwl, hmd, ↓reduceIte, hst, bind_eq_bind, bind_value, hq₁, h1]
        · rw [Poly.remainderSteps.eq_1]
          simp only [hwl, hmd, ↓reduceIte, hst, bind_eq_bind, bind_value, h2]
        · rw [← hi, hq₁i, hw'i]
          ring
      · refine ⟨q, w, ?_, ?_, hq, hw, rfl, ?_⟩
        · rw [Poly.longDivision.eq_1]
          simp only [hwl, hmd, ↓reduceIte]
        · rw [Poly.remainderSteps.eq_1]
          simp only [hwl, hmd, ↓reduceIte]
        · rw [hwd]
          exact_mod_cast not_le.1 hmd

/-! ## Division with remainder -/

/-- The degree of a canonical polynomial lies below the fuel `deg a + 1` of the
loops. -/
public theorem degree_lt_fuel {a : Poly E} (ha : a.Canonical M p) :
    (a.interpret M p).degree < ((a.degree.getD 0 + 1 : ℕ) : WithBot ℕ) := by
  rw [degree_interpret M p ha]
  cases a.degree with
  | none => exact WithBot.bot_lt_coe _
  | some d =>
    rw [Option.getD_some, Nat.cast_withBot]
    exact WithBot.coe_lt_coe.2 (Nat.lt_succ_self d)

/-- Division by the zero polynomial is `DivisionByZero`. -/
public theorem divRem_zero (a : Poly E) :
    Poly.divRem F p a Poly.zero = .fault (.field .divisionByZero) := rfl

/-- The remainder by the zero polynomial is `DivisionByZero`. -/
public theorem rem_zero (a : Poly E) :
    Poly.rem F p a Poly.zero = .fault (.field .divisionByZero) := rfl

/-- Division with remainder of canonical polynomials by a nonzero divisor
returns the canonical quotient and remainder with `A = q B + r` and
`deg r < deg B`, and the remainder alone is that remainder. -/
public theorem divRem_spec (hF : ExactField F M) {a b : Poly E} (ha : a.Canonical M p)
    (hb : b.Canonical M p) (hb0 : b ≠ Poly.zero) :
    ∃ q r, Poly.divRem F p a b = .value (q, r) ∧ Poly.rem F p a b = .value r ∧
      q.Canonical M p ∧ r.Canonical M p ∧
      a.interpret M p = q.interpret M p * b.interpret M p + r.interpret M p ∧
      (r.interpret M p).degree < (b.interpret M p).degree := by
  cases hl : b.terms.getLast? with
  | none => exact absurd ((degree_eq_none_iff b).1 (by simp [Poly.degree, hl])) hb0
  | some t =>
    obtain ⟨m, l⟩ := t
    obtain ⟨hlc, hl0⟩ := ((canonical_iff M p b).1 hb).2 _ (List.mem_of_getLast? hl)
    obtain ⟨u, hu, huc, hlu⟩ := hF.2.inverse p l hlc hl0
    obtain ⟨q, r, h1, h2, hqc, hrc, hi, hrd⟩ :=
      longDivision_spec hF hb hl huc hlu _ Poly.zero a (canonical_zero M p) ha (degree_lt_fuel ha)
    refine ⟨q, r, ?_, ?_, hqc, hrc, by rw [← hi]; simp, ?_⟩
    · simp only [Poly.divRem, hl, hu, ofOutcome_value, bind_eq_bind, bind_value, h1]
    · simp only [Poly.rem, hl, hu, ofOutcome_value, bind_eq_bind, bind_value, h2]
    · rw [(degree_interpret_of_getLast? M p hb hl).1]
      exact hrd

/-- The remainder of canonical polynomials by a nonzero divisor: a canonical
polynomial below the degree of the divisor that differs from the dividend by
a multiple of the divisor. -/
public theorem rem_spec (hF : ExactField F M) {a b : Poly E} (ha : a.Canonical M p)
    (hb : b.Canonical M p) (hb0 : b ≠ Poly.zero) :
    ∃ r, Poly.rem F p a b = .value r ∧ r.Canonical M p ∧
      (r.interpret M p).degree < (b.interpret M p).degree ∧
      ∃ Q, a.interpret M p = Q * b.interpret M p + r.interpret M p := by
  obtain ⟨q, r, -, h2, -, hrc, hi, hrd⟩ := divRem_spec hF ha hb hb0
  exact ⟨r, h2, hrc, hrd, q.interpret M p, hi⟩

/-! ## The monic form -/

/-- The monic form of a canonical polynomial is canonical and denotes it times
the inverse of its leading coefficient, zero for zero. -/
public theorem monicForm_spec (hF : ExactField F M) {a : Poly E} (ha : a.Canonical M p) :
    Poly.Yields M p (Poly.monicForm F p a)
      (a.interpret M p * C (a.interpret M p).leadingCoeff⁻¹) := by
  unfold Poly.monicForm
  cases hl : a.leadingCoefficient with
  | none =>
    have ha0 : a = Poly.zero := (leadingCoefficient_eq_none_iff a).1 hl
    subst ha0
    exact ⟨Poly.zero, rfl, canonical_zero M p, by simp⟩
  | some c =>
    obtain ⟨t, ht, htc⟩ : ∃ t, a.terms.getLast? = some t ∧ t.2 = c := by
      simpa [Poly.leadingCoefficient] using hl
    obtain ⟨hcc, hc0⟩ := ((canonical_iff M p a).1 ha).2 _ (List.mem_of_getLast? ht)
    rw [htc] at hcc hc0
    obtain ⟨u, hu, huc, hcu⟩ := hF.2.inverse p c hcc hc0
    obtain ⟨s, hs, hsc, hsi⟩ := scale_spec hF.1 huc ha
    refine ⟨s, ?_, hsc, ?_⟩
    · simp only [hu, ofOutcome_value, bind_eq_bind, bind_value, hs]
    · rw [hsi, leadingCoeff_interpret M p ha, hl]
      simp only [Option.map_some, Option.getD_some]
      rw [mul_comm, inv_eq_of_mul_eq_one_right hcu]

end Kalyx.Proofs.Polynomials.Remainders
