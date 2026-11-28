module

public import Kalyx.Proofs.Multivariate.Canonical

/-!
# Proofs of the statements about the ring operations

One theorem for each registered statement of `Kalyx.Statements.Multivariate`
about the ring operations, whose type is exactly that statement:
`ringOperationsAreExact`. Canonical forms are unique, exist when the
coefficients have canonical forms, and are read by the zero test, as
`Kalyx.Proofs.Multivariate.Canonical` proves. On canonical operands the ring
operations and powers return canonical polynomials that denote the operations
of Mathlib's `MvPolynomial (Fin n)`:

* one, the variables and the constants are polynomials of at most one term,
  the zero polynomial when the coefficient is zero (`Canonical.monomial_yields`);
* a negation maps the coefficients, and a sum or a difference merges the terms
  of its operands; each step of a merge keeps the result canonical, above
  every monomial below the operands, and equal in meaning to the left operand
  plus a unit times the right one;
* a product normalizes the products of the terms, whose coefficients are
  canonical and whose sum denotes the product (`Canonical.normalize_yields`);
* a power squares and multiplies along the binary digits of its exponent below
  the highest, so it denotes the power; a positive power of zero is the zero
  polynomial, since both are canonical and denote zero.
-/

namespace Kalyx.Proofs.Multivariate

open Kalyx.Spec.Fields Kalyx.Spec.Multivariate Kalyx.Statements.Multivariate MvPolynomial
open Kalyx.Proofs.Multivariate.Canonical

/-- `l` is canonical, above every vector below `as` and `bs`, and denotes `as` plus `s · bs`. -/
private abbrev Merged {P E : Type} {K : P → Type} [∀ p, CommRing (K p)] {n : ℕ}
    (M : Model P E K) (p : P) (o : OrderKind n) (s : K p) (as bs l : List (Exponents n × E)) :
    Prop :=
  (⟨l⟩ : MvPoly n E).Canonical M p o ∧
    (∀ e, (∀ y ∈ as, o.Lt e y.1) → (∀ y ∈ bs, o.Lt e y.1) → ∀ x ∈ l, o.Lt e x.1) ∧
    (⟨l⟩ : MvPoly n E).interpret M p =
      (⟨as⟩ : MvPoly n E).interpret M p + C s * (⟨bs⟩ : MvPoly n E).interpret M p

variable {P E : Type} {K : P → Type} [∀ p, CommRing (K p)] {R : CoefficientRing P E Empty}
  {M : Model P E K} {p : P} {n : ℕ}

/-! ## Merges -/

section Merge

variable {o : OrderKind n} {s : K p} {combine : E → E → Outcome E} {alone : E → Outcome E}

/-- Mapping the coefficients by `f`, which multiplies them by the unit `s`, merges no terms. -/
private theorem mapCoefficients_spec {f : E → Outcome E} (hs : IsUnit s)
    (hf : ∀ c, (M p).canonical c → M.Yields p (f c) (s * (M p).interpret c)) :
    ∀ l : List (Exponents n × E), (⟨l⟩ : MvPoly n E).Canonical M p o →
      ∃ l', MvPoly.mapCoefficients f l = .value l' ∧ Merged M p o s [] l l' := by
  intro l
  induction l with
  | nil => exact fun _ => ⟨[], rfl, canonical_zero M p o, by simp, by simp⟩
  | cons t l ih =>
    intro hl
    obtain ⟨d, a⟩ := t
    obtain ⟨hlt, ⟨ha, ha0⟩, hl'⟩ := (canonical_cons_iff M p o (d, a) l).1 hl
    obtain ⟨c, hfc, hc, hci⟩ := hf a ha
    obtain ⟨l', h', hl'c, hlb, hli⟩ := ih hl'
    refine ⟨(d, c) :: l', by simp [MvPoly.mapCoefficients, hfc, h'], ?_, ?_, ?_⟩
    · refine (canonical_cons_iff M p o _ _).2 ⟨hlb d (by simp) hlt, ⟨hc, ?_⟩, hl'c⟩
      rw [hci]
      exact fun h => ha0 (hs.mul_right_eq_zero.1 h)
    · intro e _ he
      obtain ⟨he₁, he₂⟩ := List.forall_mem_cons.1 he
      exact List.forall_mem_cons.2 ⟨he₁, hlb e (by simp) he₂⟩
    · simp only [interpret_cons, hli, hci, mul_add, C_mul_monomial, interpret_nil, zero_add]

/-- One step of a merge, whose `rest` merges the terms `as` after `t`. -/
private theorem mergeStep_spec (hz : ZeroTestExact R M) (hs : IsUnit s)
    (hcomb : ∀ c c', (M p).canonical c → (M p).canonical c' →
      M.Yields p (combine c c') ((M p).interpret c + s * (M p).interpret c'))
    (halone : ∀ c, (M p).canonical c → M.Yields p (alone c) (s * (M p).interpret c))
    {t : Exponents n × E} {as : List (Exponents n × E)}
    (ht : (⟨t :: as⟩ : MvPoly n E).Canonical M p o)
    {rest : List (Exponents n × E) → MvResult (List (Exponents n × E))}
    (hrest : ∀ bs, (⟨bs⟩ : MvPoly n E).Canonical M p o →
      ∃ l, rest bs = .value l ∧ Merged M p o s as bs l) :
    ∀ bs, (⟨bs⟩ : MvPoly n E).Canonical M p o →
      ∃ l, MvPoly.mergeStep R p o combine alone t rest bs = .value l ∧
        Merged M p o s (t :: as) bs l := by
  obtain ⟨hta, htc, -⟩ := (canonical_cons_iff M p o t as).1 ht
  intro bs
  induction bs with
  | nil =>
    intro _
    obtain ⟨l, hl, hlc, hlb, hli⟩ := hrest [] (canonical_zero M p o)
    refine ⟨t :: l, by simp [MvPoly.mergeStep, hl], ?_, ?_, ?_⟩
    · exact (canonical_cons_iff M p o t l).2 ⟨hlb t.1 hta (by simp), htc, hlc⟩
    · intro e he _
      obtain ⟨he₁, he₂⟩ := List.forall_mem_cons.1 he
      exact List.forall_mem_cons.2 ⟨he₁, hlb e he₂ (by simp)⟩
    · simp only [interpret_cons, hli, interpret_nil]
      ring
  | cons u us ih =>
    intro hbs
    obtain ⟨hub, huc, hus⟩ := (canonical_cons_iff M p o u us).1 hbs
    cases h : o.compare t.1 u.1 with
    | lt =>
      have hlt := (compare_eq_lt_iff o _ _).1 h
      obtain ⟨l, hl, hlc, hlb, hli⟩ := hrest (u :: us) hbs
      refine ⟨t :: l, by simp [MvPoly.mergeStep, h, hl], ?_, ?_, ?_⟩
      · refine (canonical_cons_iff M p o t l).2 ⟨hlb t.1 hta ?_, htc, hlc⟩
        exact List.forall_mem_cons.2 ⟨hlt, fun y hy => orderLt_trans o hlt (hub y hy)⟩
      · intro e he hb
        exact List.forall_mem_cons.2 ⟨(List.forall_mem_cons.1 he).1,
          hlb e (List.forall_mem_cons.1 he).2 hb⟩
      · simp only [interpret_cons, hli]
        ring
    | eq =>
      have heq := (compare_eq_eq_iff o _ _).1 h
      obtain ⟨c, hc, hcc, hci⟩ := hcomb t.2 u.2 htc.1 huc.1
      obtain ⟨l, hl, hlc, hlb, hli⟩ := hrest us hus
      have hlb' : ∀ e, (∀ y ∈ t :: as, o.Lt e y.1) → (∀ y ∈ u :: us, o.Lt e y.1) →
          ∀ x ∈ l, o.Lt e x.1 := fun e he hb =>
        hlb e (List.forall_mem_cons.1 he).2 (List.forall_mem_cons.1 hb).2
      have hmi : monomial t.1.toFinsupp ((M p).interpret t.2) +
          C s * monomial u.1.toFinsupp ((M p).interpret u.2) =
            monomial t.1.toFinsupp ((M p).interpret c) := by
        rw [C_mul_monomial, ← heq, hci, map_add]
      by_cases h0 : (M p).interpret c = 0
      · refine ⟨l, ?_, hlc, hlb', ?_⟩
        · simp [MvPoly.mergeStep, h, hc, testZero_of_eq_zero p hz hcc h0, hl]
        · rw [h0, map_zero] at hmi
          simp only [interpret_cons, hli]
          linear_combination -hmi
      · refine ⟨(t.1, c) :: l, ?_, ?_, ?_, ?_⟩
        · simp [MvPoly.mergeStep, h, hc, testZero_of_ne_zero p hz hcc h0, hl]
        · refine (canonical_cons_iff M p o _ l).2 ⟨hlb t.1 hta ?_, ⟨hcc, h0⟩, hlc⟩
          exact fun y hy => heq ▸ hub y hy
        · intro e he hb
          exact List.forall_mem_cons.2 ⟨(List.forall_mem_cons.1 he).1, hlb' e he hb⟩
        · simp only [interpret_cons, hli]
          linear_combination -hmi
    | gt =>
      have hgt := (compare_eq_gt_iff o _ _).1 h
      obtain ⟨c, hc, hcc, hci⟩ := halone u.2 huc.1
      obtain ⟨l, hl, hlc, hlb, hli⟩ := ih hus
      refine ⟨(u.1, c) :: l, by simp [MvPoly.mergeStep, h, hc, hl], ?_, ?_, ?_⟩
      · refine (canonical_cons_iff M p o _ l).2 ⟨hlb u.1 ?_ hub, ⟨hcc, ?_⟩, hlc⟩
        · exact List.forall_mem_cons.2 ⟨hgt, fun y hy => orderLt_trans o hgt (hta y hy)⟩
        · rw [hci]
          exact fun h => huc.2 (hs.mul_right_eq_zero.1 h)
      · intro e he hb
        exact List.forall_mem_cons.2 ⟨(List.forall_mem_cons.1 hb).1,
          hlb e he (List.forall_mem_cons.1 hb).2⟩
      · simp only [interpret_cons, hli, hci, mul_add, C_mul_monomial]
        ring

/-- The merge of two canonical lists. -/
private theorem merge_spec (hz : ZeroTestExact R M) (hs : IsUnit s)
    (hcomb : ∀ c c', (M p).canonical c → (M p).canonical c' →
      M.Yields p (combine c c') ((M p).interpret c + s * (M p).interpret c'))
    (halone : ∀ c, (M p).canonical c → M.Yields p (alone c) (s * (M p).interpret c)) :
    ∀ as bs : List (Exponents n × E), (⟨as⟩ : MvPoly n E).Canonical M p o →
      (⟨bs⟩ : MvPoly n E).Canonical M p o →
      ∃ l, MvPoly.merge R p o combine alone as bs = .value l ∧ Merged M p o s as bs l := by
  intro as
  induction as with
  | nil =>
    intro bs _ hbs
    rw [MvPoly.merge]
    exact mapCoefficients_spec hs halone bs hbs
  | cons t as ih =>
    intro bs ht hbs
    rw [MvPoly.merge]
    exact mergeStep_spec hz hs hcomb halone ht
      (fun bs hbs => ih bs ((canonical_cons_iff M p o t as).1 ht).2.2 hbs) bs hbs

end Merge

/-! ## Products -/

/-- The products of a term with a canonical coefficient with a list of such terms. -/
private theorem scaledTerms_spec (hR : RingLaws R M) {t : Exponents n × E}
    (ht : (M p).canonical t.2) :
    ∀ bs : List (Exponents n × E), (∀ x ∈ bs, (M p).canonical x.2) →
      ∃ l, MvPoly.scaledTerms R p t bs = .value l ∧ (∀ x ∈ l, (M p).canonical x.2) ∧
        (⟨l⟩ : MvPoly n E).interpret M p =
          monomial t.1.toFinsupp ((M p).interpret t.2) * (⟨bs⟩ : MvPoly n E).interpret M p := by
  intro bs
  induction bs with
  | nil => exact fun _ => ⟨[], rfl, by simp, by simp⟩
  | cons u us ih =>
    intro hbs
    obtain ⟨hu, hus⟩ := List.forall_mem_cons.1 hbs
    obtain ⟨c, hc, hcc, hci⟩ := hR.multiply p t.2 u.2 ht hu
    obtain ⟨l, hl, hlc, hli⟩ := ih hus
    refine ⟨(t.1.product u.1, c) :: l, by simp [MvPoly.scaledTerms, hc, hl],
      List.forall_mem_cons.2 ⟨hcc, hlc⟩, ?_⟩
    simp only [interpret_cons, hli, hci, mul_add, monomial_mul_monomial,
      monomialOrdersRespectProducts.1 n]

/-- The products of the terms of two lists with canonical coefficients. -/
private theorem termProducts_spec (hR : RingLaws R M) {bs : List (Exponents n × E)}
    (hbs : ∀ x ∈ bs, (M p).canonical x.2) :
    ∀ as : List (Exponents n × E), (∀ x ∈ as, (M p).canonical x.2) →
      ∃ l, MvPoly.termProducts R p bs as = .value l ∧ (∀ x ∈ l, (M p).canonical x.2) ∧
        (⟨l⟩ : MvPoly n E).interpret M p =
          (⟨as⟩ : MvPoly n E).interpret M p * (⟨bs⟩ : MvPoly n E).interpret M p := by
  intro as
  induction as with
  | nil => exact fun _ => ⟨[], rfl, by simp, by simp⟩
  | cons t ts ih =>
    intro has
    obtain ⟨ht, hts⟩ := List.forall_mem_cons.1 has
    obtain ⟨w, hw, hwc, hwi⟩ := scaledTerms_spec hR ht bs hbs
    obtain ⟨l, hl, hlc, hli⟩ := ih hts
    refine ⟨w ++ l, by simp [MvPoly.termProducts, hw, hl], fun x hx => ?_, ?_⟩
    · rcases List.mem_append.1 hx with hx | hx
      exacts [hwc x hx, hlc x hx]
    · rw [interpret_append, hwi, hli, interpret_cons]
      ring

/-! ## The operations -/

/-- The vector of the constant monomial is zero. -/
private theorem toFinsupp_constant : (Exponents.constant : Exponents n).toFinsupp = 0 := by
  ext i
  simp [Exponents.constant]

section Operations

variable (hR : ExactRing R M) (r : MultivariateRing P n)
include hR

/-- `one` yields `1`. -/
private theorem one_yields : r.Yields M (r.one R) 1 := by
  have h := monomial_yields hR r Exponents.constant (hR.1.one r.coefficients).1
  rwa [(hR.1.one r.coefficients).2, toFinsupp_constant, ← C_apply, C_1] at h

/-- `generator` yields the variable. -/
private theorem generator_yields (i : Fin n) : r.Yields M (r.generator R i) (X i) := by
  have h := monomial_yields hR r (Exponents.generator i) (hR.1.one r.coefficients).1
  have hg : (Exponents.generator i).toFinsupp = Finsupp.single i 1 := by
    ext j
    simp [Exponents.generator, Finsupp.single_apply, eq_comm]
  rwa [(hR.1.one r.coefficients).2, hg] at h

/-- `constant` of a canonical element yields the constant. -/
private theorem constant_yields {c : E} (hc : (M r.coefficients).canonical c) :
    r.Yields M (r.constant R c) (C ((M r.coefficients).interpret c)) := by
  have h := monomial_yields hR r Exponents.constant hc
  rwa [toFinsupp_constant, ← C_apply] at h

variable {a b : MvPoly n E} (ha : a.Canonical M r.coefficients r.order)
  (hb : b.Canonical M r.coefficients r.order)
include ha

/-- `negate` yields the negation. -/
private theorem negate_yields : r.Yields M (r.negate R a) (-a.interpret M r.coefficients) := by
  obtain ⟨as⟩ := a
  obtain ⟨l, hl, hlc, -, hli⟩ := mapCoefficients_spec (s := -1) isUnit_one.neg
    (fun c hc => by rw [neg_one_mul]; exact hR.1.negate _ c hc) as ha
  exact ⟨⟨l⟩, by simp [MultivariateRing.negate, hl, MvResult.map], hlc,
    by simp [MultivariateRing.model, hli]⟩

include hb

/-- `add` yields the sum. -/
private theorem add_yields :
    r.Yields M (r.add R a b) (a.interpret M r.coefficients + b.interpret M r.coefficients) := by
  obtain ⟨as⟩ := a
  obtain ⟨bs⟩ := b
  obtain ⟨l, hl, hlc, -, hli⟩ := merge_spec (combine := R.add r.coefficients)
    (alone := Outcome.value) (s := 1) hR.2 isUnit_one
    (fun c c' hc hc' => by rw [one_mul]; exact hR.1.add _ c c' hc hc')
    (fun c hc => ⟨c, rfl, hc, by rw [one_mul]⟩) as bs ha hb
  exact ⟨⟨l⟩, by simp [MultivariateRing.add, hl, MvResult.map], hlc,
    by simp [MultivariateRing.model, hli]⟩

/-- `subtract` yields the difference. -/
private theorem subtract_yields :
    r.Yields M (r.subtract R a b)
      (a.interpret M r.coefficients - b.interpret M r.coefficients) := by
  obtain ⟨as⟩ := a
  obtain ⟨bs⟩ := b
  obtain ⟨l, hl, hlc, -, hli⟩ := merge_spec (combine := R.subtract r.coefficients)
    (alone := R.negate r.coefficients) (s := -1) hR.2 isUnit_one.neg
    (fun c c' hc hc' => by rw [neg_one_mul, ← sub_eq_add_neg]; exact hR.1.subtract _ c c' hc hc')
    (fun c hc => by rw [neg_one_mul]; exact hR.1.negate _ c hc) as bs ha hb
  exact ⟨⟨l⟩, by simp [MultivariateRing.subtract, hl, MvResult.map], hlc,
    by simp [MultivariateRing.model, hli, sub_eq_add_neg]⟩

/-- `multiply` yields the product. -/
private theorem multiply_yields :
    r.Yields M (r.multiply R a b)
      (a.interpret M r.coefficients * b.interpret M r.coefficients) := by
  obtain ⟨as⟩ := a
  obtain ⟨bs⟩ := b
  have coeffs : ∀ {l : List (Exponents n × E)},
      (⟨l⟩ : MvPoly n E).Canonical M r.coefficients r.order →
        ∀ x ∈ l, (M r.coefficients).canonical x.2 :=
    fun h x hx => (((canonical_iff_terms M _ _ _).1 h).2 x hx).1
  obtain ⟨l, hl, hlc, hli⟩ := termProducts_spec hR.1 (coeffs hb) as (coeffs ha)
  have hm : r.multiply R ⟨as⟩ ⟨bs⟩ = r.normalize R l := by
    simp [MultivariateRing.multiply, hl]
  rw [hm, ← hli]
  exact normalize_yields hR r hlc

end Operations

/-! ## Powers -/

/-- No digits remain of zero. -/
private theorem binaryDigitsFrom_zero (fuel : ℕ) (acc : List Bool) :
    binaryDigitsFrom fuel 0 acc = acc := by
  cases fuel <;> simp [binaryDigitsFrom]

/-- The digits of `k`, read from the highest after the digits `acc`, give `k` then `acc`. -/
private theorem foldl_binaryDigitsFrom :
    ∀ (fuel k : ℕ) (acc : List Bool), k ≤ fuel →
      (binaryDigitsFrom fuel k acc).foldl (fun m b => 2 * m + b.toNat) 0 =
        acc.foldl (fun m b => 2 * m + b.toNat) k := by
  intro fuel
  induction fuel with
  | zero =>
    intro k acc hk
    obtain rfl : k = 0 := by omega
    rfl
  | succ fuel ih =>
    intro k acc hk
    by_cases h0 : k = 0
    · subst h0
      rw [binaryDigitsFrom_zero]
    · simp only [binaryDigitsFrom, h0, ↓reduceIte]
      rw [ih (k / 2) _ (by omega), List.foldl_cons]
      congr 1
      rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [h] <;> omega

/-- The binary digits of a positive `k` start with `1`. -/
private theorem binaryDigitsFrom_head :
    ∀ (fuel k : ℕ) (acc : List Bool), 0 < k → k ≤ fuel →
      ∃ ds, binaryDigitsFrom fuel k acc = true :: ds := by
  intro fuel
  induction fuel with
  | zero => intro k acc h1 h2; omega
  | succ fuel ih =>
    intro k acc h1 h2
    simp only [binaryDigitsFrom, show k ≠ 0 by omega, ↓reduceIte]
    by_cases h : k / 2 = 0
    · obtain rfl : k = 1 := by omega
      exact ⟨acc, by simp [binaryDigitsFrom_zero]⟩
    · exact ih (k / 2) _ (by omega) (by omega)

/-- The binary digits of a positive `k` are `1` and digits that give `k` after it. -/
private theorem binaryDigits_of_pos {k : ℕ} (hk : 0 < k) :
    ∃ ds, binaryDigits k = true :: ds ∧ ds.foldl (fun m b => 2 * m + b.toNat) 1 = k := by
  obtain ⟨ds, hds⟩ := binaryDigitsFrom_head k k [] hk le_rfl
  refine ⟨ds, hds, ?_⟩
  have := foldl_binaryDigitsFrom k k [] le_rfl
  rw [hds, List.foldl_cons] at this
  simpa using this

/-- A result that yields `x`, passed on to `f`, which yields `y` from every canonical `x`. -/
private theorem yields_bind {r : MultivariateRing P n} {o : MvResult (MvPoly n E)}
    {f : MvPoly n E → MvResult (MvPoly n E)} {x y : MvPolynomial (Fin n) (K r.coefficients)}
    (h : r.Yields M o x)
    (hf : ∀ v, v.Canonical M r.coefficients r.order → v.interpret M r.coefficients = x →
      r.Yields M (f v) y) :
    r.Yields M (o >>= f) y := by
  obtain ⟨v, rfl, hv, hvx⟩ := h
  exact hf v hv hvx

section Powers

variable (hR : ExactRing R M) (r : MultivariateRing P n) {a : MvPoly n E}
  (ha : a.Canonical M r.coefficients r.order)
include hR ha

/-- The loop of a power from `s`, which denotes `Aʲ`, over the digits `ds`. -/
private theorem power_loop :
    ∀ (ds : List Bool) (s : MvPoly n E) (j : ℕ), s.Canonical M r.coefficients r.order →
      s.interpret M r.coefficients = a.interpret M r.coefficients ^ j →
      r.Yields M (ds.foldlM (init := s) fun s digit => do
          let s ← r.multiply R s s
          if digit then r.multiply R s a else pure s)
        (a.interpret M r.coefficients ^ ds.foldl (fun m b => 2 * m + b.toNat) j) := by
  intro ds
  induction ds with
  | nil => exact fun s j hs hsj => ⟨s, rfl, hs, hsj⟩
  | cons b ds ih =>
    intro s j hs hsj
    rw [List.foldlM_cons, List.foldl_cons]
    refine yields_bind (x := a.interpret M r.coefficients ^ (2 * j + b.toNat)) ?_
      fun w hw hwi => ih w _ hw hwi
    refine yields_bind (multiply_yields hR r hs hs) fun v hv hvi => ?_
    have hv' : v.interpret M r.coefficients = a.interpret M r.coefficients ^ (2 * j) := by
      rw [hvi, hsj, two_mul, pow_add]
    cases b with
    | false => exact ⟨v, rfl, hv, by rw [Bool.toNat_false, add_zero]; exact hv'⟩
    | true =>
      have := multiply_yields hR r hv ha
      rw [hv', ← pow_succ] at this
      exact this

/-- `power` yields the power. -/
private theorem power_yields (k : ℕ) :
    r.Yields M (r.power R a k) (a.interpret M r.coefficients ^ k) := by
  unfold MultivariateRing.power
  split
  · rename_i hk
    rw [hk, pow_zero]
    exact one_yields hR r
  · rename_i hk
    obtain ⟨ds, hds, hval⟩ := binaryDigits_of_pos (Nat.pos_of_ne_zero hk)
    rw [hds, List.tail_cons, ← hval]
    exact power_loop hR r ha ds a 1 ha (pow_one _).symm

end Powers

/-- Proves `RingOperationsAreExact`. -/
public theorem ringOperationsAreExact : RingOperationsAreExact := by
  intro P E K _ R M hR n r
  dsimp only
  have hzero : ∀ k, 1 ≤ k → r.power R MvPoly.zero k = .value MvPoly.zero := fun k hk =>
    eq_of_yields (hR.1.unique _) (power_yields hR r (canonical_zero M _ _) k)
      (by rw [interpret_zero, zero_pow (by omega)]; exact yields_zero r)
  exact ⟨Canonical.unique hR r, Canonical.complete hR r, Canonical.canonical_iff hR r,
    yields_zero r, one_yields hR r, generator_yields hR r, fun _ => constant_yields hR r,
    fun _ ha => ⟨negate_yields hR r ha, power_yields hR r ha⟩,
    fun _ _ ha hb => ⟨add_yields hR r ha hb, subtract_yields hR r ha hb,
      multiply_yields hR r ha hb⟩,
    fun _ => rfl, hzero⟩

end Kalyx.Proofs.Multivariate
