module

public import Kalyx.Proofs.Polynomials.Operations

/-!
# The checks, binary digits and the operations of a ring

An unregistered helper module of the proofs about the univariate polynomials;
it proves no registered statement. It holds:

* the checks of the limits: a check passes its value on or reports
  `ResourceLimit` naming `max_exponent`, `max_nodes` or `max_storage_bytes`
  (`checkDegree_eq`, `checkStorage_eq`, `check_eq`), so a result that a check
  takes is the value or such a limit (`YieldsWithinLimits`, with
  `ywl_bind`, `ywl_check`, `ywl_bind_check`, `ywl_checkDegree`);
* the binary digits of `k`, the highest first, read back into `k`
  (`binaryDigits_value`), whose first digit is `1` for `k ≥ 1`
  (`binaryDigits_of_pos`), and the induction over a loop on the digits whose
  every step is a value (`foldlM_digits`, `foldlM_binaryDigits`);
* the operations of a ring under limits over a coefficient ring that is exact:
  each returns a canonical polynomial that denotes the operation of Mathlib's
  `Polynomial`, or `ResourceLimit` (`zero_ywl` to `power_ywl`), the product
  with every partial sum of its rows checked; the power by `0` is the
  polynomial one, and a positive power of zero within the bound on exponents
  is the checked zero polynomial (`power_zero_exponent`, `power_zero_base`).
-/

namespace Kalyx.Proofs.Polynomials.Checks

open Kalyx.Spec.Fields Kalyx.Spec.Polynomials Kalyx.Statements.Polynomials Polynomial
open Kalyx.Spec.Terms (exponentBound)
open Kalyx.Proofs.Polynomials.Canonical Kalyx.Proofs.Polynomials.Operations

/-! ## Checks -/

section Checks

variable {α : Type}

/-- The check of a degree passes on `next ()` or reports `max_exponent`. -/
public theorem checkDegree_eq (L : Limits) (d : ℕ) (next : Unit → PolyResult α) :
    checkDegree L d next = next () ∨ checkDegree L d next = .resourceLimit .exponent := by
  unfold checkDegree
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The check of a degree within the bound passes on `next ()`. -/
public theorem checkDegree_of_le (L : Limits) {d : ℕ} (h : d ≤ exponentBound L.maxExponent)
    (next : Unit → PolyResult α) : checkDegree L d next = next () := by
  simp [checkDegree, not_lt.2 h]

/-- The check of a storage cost passes on `next ()` or reports `max_nodes` or
`max_storage_bytes`. -/
public theorem checkStorage_eq (L : Limits) (s : Storage) (next : Unit → PolyResult α) :
    checkStorage L s next = next () ∨ checkStorage L s next = .resourceLimit .nodes ∨
      checkStorage L s next = .resourceLimit .storageBytes := by
  unfold checkStorage
  split
  · exact Or.inr (Or.inl rfl)
  · split
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl rfl

/-- The check of a polynomial passes it on or reports `ResourceLimit` naming
`max_exponent`, `max_nodes` or `max_storage_bytes`. -/
public theorem check_eq {P E U : Type} (R : CoefficientRing P E U) (L : Limits)
    (r : PolynomialRing P) (a : Poly E) :
    r.check R L a = .value a ∨ r.check R L a = .resourceLimit .exponent ∨
      r.check R L a = .resourceLimit .nodes ∨ r.check R L a = .resourceLimit .storageBytes := by
  unfold PolynomialRing.check
  rcases checkDegree_eq L (a.degree.getD 0)
      (fun _ => checkStorage L (r.storage R a) fun _ => .value a) with h | h <;> rw [h]
  · rcases checkStorage_eq L (r.storage R a) (fun _ => .value a) with h' | h' | h' <;> rw [h'] <;>
      simp
  · simp

end Checks

/-! ## Results within the limits -/

section Within

variable {P E : Type} {K : P → Type} [∀ p, CommRing (K p)] {M : Model P E K} {p : P}

/-- A canonical result is within the limits. -/
public theorem ywl_of_yields {o : PolyResult (Poly E)} {x : Polynomial (K p)}
    (h : Poly.Yields M p o x) : YieldsWithinLimits M p o x := Or.inl h

/-- A result within the limits, passed by `bind` to a step that is within the
limits on each canonical value that denotes it. -/
public theorem ywl_bind {o : PolyResult (Poly E)} {f : Poly E → PolyResult (Poly E)}
    {x y : Polynomial (K p)} (h : YieldsWithinLimits M p o x)
    (hf : ∀ v, v.Canonical M p → v.interpret M p = x → YieldsWithinLimits M p (f v) y) :
    YieldsWithinLimits M p (o.bind f) y := by
  rcases h with ⟨v, rfl, hv, hvx⟩ | rfl | rfl | rfl
  · exact hf v hv hvx
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

/-- A check of a degree keeps a result within the limits. -/
public theorem ywl_checkDegree (L : Limits) (d : ℕ) {next : Unit → PolyResult (Poly E)}
    {x : Polynomial (K p)} (h : YieldsWithinLimits M p (next ()) x) :
    YieldsWithinLimits M p (checkDegree L d next) x := by
  rcases checkDegree_eq L d next with e | e <;> rw [e]
  · exact h
  · exact Or.inr (Or.inl rfl)

/-- The check of a canonical polynomial is within the limits. -/
public theorem ywl_check {U : Type} (R : CoefficientRing P E U) (L : Limits)
    (r : PolynomialRing P) {a : Poly E} (ha : a.Canonical M r.coefficients) :
    YieldsWithinLimits M r.coefficients (r.check R L a) (a.interpret M r.coefficients) := by
  rcases check_eq R L r a with e | e | e | e <;> rw [e]
  · exact Or.inl ⟨a, rfl, ha, rfl⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

/-- A canonical result, then checked, is within the limits. -/
public theorem ywl_bind_check {U : Type} (R : CoefficientRing P E U) (L : Limits)
    (r : PolynomialRing P) {o : PolyResult (Poly E)} {x : Polynomial (K r.coefficients)}
    (h : Poly.Yields M r.coefficients o x) :
    YieldsWithinLimits M r.coefficients (o.bind fun a => r.check R L a) x :=
  ywl_bind (ywl_of_yields h) fun _ hv hvx => hvx ▸ ywl_check R L r hv

end Within

/-! ## Binary digits -/

/-- No digits remain of zero. -/
public theorem binaryDigitsFrom_zero (fuel : ℕ) (acc : List Bool) :
    binaryDigitsFrom fuel 0 acc = acc := by
  cases fuel <;> simp [binaryDigitsFrom]

/-- The digits of `n`, read from the highest after the digits already read,
give `n` followed by those digits. -/
public theorem foldl_binaryDigitsFrom :
    ∀ (fuel n : ℕ) (acc : List Bool), n ≤ fuel →
      (binaryDigitsFrom fuel n acc).foldl (fun m b => 2 * m + b.toNat) 0 =
        acc.foldl (fun m b => 2 * m + b.toNat) n := by
  intro fuel
  induction fuel with
  | zero =>
    intro n acc hn
    obtain rfl : n = 0 := by omega
    rfl
  | succ fuel ih =>
    intro n acc hn
    by_cases h0 : n = 0
    · subst h0
      rw [binaryDigitsFrom_zero]
    · simp only [binaryDigitsFrom, h0, ↓reduceIte]
      rw [ih (n / 2) _ (by omega), List.foldl_cons]
      congr 1
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega

/-- The binary digits of `k`, read from the highest, give `k`. -/
public theorem binaryDigits_value (k : ℕ) :
    (binaryDigits k).foldl (fun m b => 2 * m + b.toNat) 0 = k :=
  foldl_binaryDigitsFrom k k [] le_rfl

/-- The binary digits of a positive `n` start with `1`. -/
public theorem binaryDigitsFrom_head :
    ∀ (fuel n : ℕ) (acc : List Bool), 0 < n → n ≤ fuel →
      ∃ ds, binaryDigitsFrom fuel n acc = true :: ds := by
  intro fuel
  induction fuel with
  | zero => intro n acc h1 h2; omega
  | succ fuel ih =>
    intro n acc h1 h2
    simp only [binaryDigitsFrom, show n ≠ 0 by omega, ↓reduceIte]
    by_cases h : n / 2 = 0
    · have hn : n = 1 := by omega
      subst hn
      exact ⟨acc, by simp [binaryDigitsFrom_zero]⟩
    · exact ih (n / 2) _ (by omega) (by omega)

/-- The binary digits of a positive `k` are `1` followed by digits that give
`k` when read after the leading `1`. -/
public theorem binaryDigits_of_pos {k : ℕ} (hk : 0 < k) :
    ∃ ds, binaryDigits k = true :: ds ∧ ds.foldl (fun m b => 2 * m + b.toNat) 1 = k := by
  obtain ⟨ds, hds⟩ := binaryDigitsFrom_head k k [] hk le_rfl
  refine ⟨ds, hds, ?_⟩
  have := binaryDigits_value k
  rw [binaryDigits, hds, List.foldl_cons] at this
  simpa using this

/-- The binary digits of `0` are none. -/
public theorem binaryDigits_zero : binaryDigits 0 = [] := rfl

/-- A loop over binary digits whose every step is a value: when each step
from a state with the invariant at `j` returns a state with the invariant at
`2 j` plus the digit, the loop returns a state with the invariant at the
number that the digits give when read after `j`. -/
public theorem foldlM_digits {α : Type} (Inv : α → ℕ → Prop) (f : α → Bool → PolyResult α)
    (hf : ∀ s j b, Inv s j → ∃ s', f s b = .value s' ∧ Inv s' (2 * j + b.toNat)) :
    ∀ (ds : List Bool) (s : α) (j : ℕ), Inv s j →
      ∃ s', ds.foldlM f s = .value s' ∧ Inv s' (ds.foldl (fun m b => 2 * m + b.toNat) j) := by
  intro ds
  induction ds with
  | nil => exact fun s j h => ⟨s, rfl, h⟩
  | cons b ds ih =>
    intro s j h
    obtain ⟨s', hs', h'⟩ := hf s j b h
    obtain ⟨s'', hs'', h''⟩ := ih s' _ h'
    exact ⟨s'', by rw [List.foldlM_cons, bind_eq_bind, hs', bind_value, hs''], h''⟩

/-- A loop over all the binary digits of `k` from a state with the invariant
at `0`, whose every step is a value as in `foldlM_digits`, returns a state
with the invariant at `k`. -/
public theorem foldlM_binaryDigits {α : Type} (Inv : α → ℕ → Prop) (f : α → Bool → PolyResult α)
    (hf : ∀ s j b, Inv s j → ∃ s', f s b = .value s' ∧ Inv s' (2 * j + b.toNat)) (k : ℕ)
    {s : α} (hs : Inv s 0) : ∃ s', (binaryDigits k).foldlM f s = .value s' ∧ Inv s' k := by
  obtain ⟨s', h, h'⟩ := foldlM_digits Inv f hf (binaryDigits k) s 0 hs
  exact ⟨s', h, binaryDigits_value k ▸ h'⟩

/-! ## The operations of a ring -/

section Ring

variable {P E : Type} {K : P → Type} [∀ p, CommRing (K p)] {R : CoefficientRing P E Empty}
  {M : Model P E K}

/-- `zero` is within the limits and denotes `0`. -/
public theorem zero_ywl (L : Limits) (r : PolynomialRing P) :
    YieldsWithinLimits M r.coefficients (r.zero R L) 0 := by
  have := ywl_check (M := M) R L r (canonical_zero M r.coefficients)
  rwa [interpret_zero] at this

/-- `one` is within the limits and denotes `1`. -/
public theorem one_ywl (hR : ExactRing R M) (L : Limits) (r : PolynomialRing P) :
    YieldsWithinLimits M r.coefficients (r.one R L) 1 := by
  have h := monomial_spec (R := R) (p := r.coefficients) hR.2 0 (hR.1.one r.coefficients).1
  rw [(hR.1.one r.coefficients).2, monomial_zero_left, map_one] at h
  exact ywl_bind_check R L r h

/-- `generator` is within the limits and denotes `X`. -/
public theorem generator_ywl (hR : ExactRing R M) (L : Limits) (r : PolynomialRing P) :
    YieldsWithinLimits M r.coefficients (r.generator R L) X := by
  have h := monomial_spec (R := R) (p := r.coefficients) hR.2 1 (hR.1.one r.coefficients).1
  rw [(hR.1.one r.coefficients).2, monomial_one_one_eq_X] at h
  exact ywl_checkDegree L 1 (ywl_bind_check R L r h)

/-- `constant` of a canonical element is within the limits and denotes the
constant. -/
public theorem constant_ywl (hR : ExactRing R M) (L : Limits) (r : PolynomialRing P) {c : E}
    (hc : (M r.coefficients).canonical c) :
    YieldsWithinLimits M r.coefficients (r.constant R L c)
      (C ((M r.coefficients).interpret c)) := by
  have h := monomial_spec (R := R) (p := r.coefficients) hR.2 0 hc
  rw [monomial_zero_left] at h
  exact ywl_bind_check R L r h

/-- `negate` of a canonical polynomial is within the limits and denotes the
negation. -/
public theorem negate_ywl (hR : ExactRing R M) (L : Limits) (r : PolynomialRing P) {a : Poly E}
    (ha : a.Canonical M r.coefficients) :
    YieldsWithinLimits M r.coefficients (r.negate R L a) (-a.interpret M r.coefficients) :=
  ywl_bind_check R L r (negate_spec hR ha)

/-- `add` of canonical polynomials is within the limits and denotes the
sum. -/
public theorem add_ywl (hR : ExactRing R M) (L : Limits) (r : PolynomialRing P) {a b : Poly E}
    (ha : a.Canonical M r.coefficients) (hb : b.Canonical M r.coefficients) :
    YieldsWithinLimits M r.coefficients (r.add R L a b)
      (a.interpret M r.coefficients + b.interpret M r.coefficients) :=
  ywl_bind_check R L r (sum_spec hR ha hb)

/-- `subtract` of canonical polynomials is within the limits and denotes the
difference. -/
public theorem subtract_ywl (hR : ExactRing R M) (L : Limits) (r : PolynomialRing P)
    {a b : Poly E} (ha : a.Canonical M r.coefficients) (hb : b.Canonical M r.coefficients) :
    YieldsWithinLimits M r.coefficients (r.subtract R L a b)
      (a.interpret M r.coefficients - b.interpret M r.coefficients) :=
  ywl_bind_check R L r (difference_spec hR ha hb)

/-- `derivative` of a canonical polynomial is within the limits and denotes
Mathlib's `derivative`. -/
public theorem derivative_ywl (hR : ExactRing R M) (L : Limits) (r : PolynomialRing P)
    {a : Poly E} (ha : a.Canonical M r.coefficients) :
    YieldsWithinLimits M r.coefficients (r.derivative R L a)
      (derivative (a.interpret M r.coefficients)) :=
  ywl_bind_check R L r (derivative_spec hR ha)

/-- The rows of a canonical list over a canonical list, with each partial sum
checked, from a canonical total, are within the limits and denote the total
plus the product of the lists. -/
public theorem rows_check_ywl (hR : ExactRing R M) (L : Limits) (r : PolynomialRing P)
    {q : List (ℕ × E)} (hq : (⟨q⟩ : Poly E).Canonical M r.coefficients) :
    ∀ (l : List (ℕ × E)) (total : Poly E), total.Canonical M r.coefficients →
      (⟨l⟩ : Poly E).Canonical M r.coefficients →
      YieldsWithinLimits M r.coefficients (Poly.rows R r.coefficients (r.check R L) q total l)
        (total.interpret M r.coefficients +
          (⟨l⟩ : Poly E).interpret M r.coefficients * (⟨q⟩ : Poly E).interpret M r.coefficients) := by
  intro l
  induction l with
  | nil => exact fun total ht _ => ywl_of_yields ⟨total, rfl, ht, by simp⟩
  | cons t l ih =>
    intro total ht hl
    obtain ⟨d, c⟩ := t
    obtain ⟨-, ⟨hc, -⟩, hl'⟩ := (canonical_cons_iff M _ (d, c) l).1 hl
    obtain ⟨w, hw, hwc, hwi⟩ := row_spec hR d hc q Poly.zero (canonical_zero M _) hq
      (by simp [Poly.zero])
    obtain ⟨u, hu, huc, hui⟩ := sum_spec hR ht hwc
    simp only [Poly.rows, bind_eq_bind, hw, bind_value, hu]
    refine ywl_bind (ywl_check R L r huc) fun v hv hvi => ?_
    have e : total.interpret M r.coefficients +
        (⟨(d, c) :: l⟩ : Poly E).interpret M r.coefficients *
          (⟨q⟩ : Poly E).interpret M r.coefficients =
        v.interpret M r.coefficients +
          (⟨l⟩ : Poly E).interpret M r.coefficients *
            (⟨q⟩ : Poly E).interpret M r.coefficients := by
      rw [hvi, hui, hwi, interpret_cons, interpret_zero]
      ring
    rw [e]
    exact ih v hv hl'

/-- The product with every partial sum checked of canonical polynomials is
within the limits and denotes the product. -/
public theorem product_check_ywl (hR : ExactRing R M) (L : Limits) (r : PolynomialRing P)
    {a b : Poly E} (ha : a.Canonical M r.coefficients) (hb : b.Canonical M r.coefficients) :
    YieldsWithinLimits M r.coefficients (Poly.product R r.coefficients (r.check R L) a b)
      (a.interpret M r.coefficients * b.interpret M r.coefficients) := by
  unfold Poly.product
  split
  · have h := rows_check_ywl hR L r (q := a.terms) ha b.terms Poly.zero
      (canonical_zero M _) hb
    simp only [interpret_zero, mk_terms, zero_add] at h
    rwa [mul_comm] at h
  · have h := rows_check_ywl hR L r (q := b.terms) hb a.terms Poly.zero
      (canonical_zero M _) ha
    simpa using h

/-- `multiply` of canonical polynomials is within the limits and denotes the
product. -/
public theorem multiply_ywl (hR : ExactRing R M) (L : Limits) (r : PolynomialRing P)
    {a b : Poly E} (ha : a.Canonical M r.coefficients) (hb : b.Canonical M r.coefficients) :
    YieldsWithinLimits M r.coefficients (r.multiply R L a b)
      (a.interpret M r.coefficients * b.interpret M r.coefficients) := by
  have h : YieldsWithinLimits M r.coefficients
      ((Poly.product R r.coefficients (r.check R L) a b).bind fun s => r.check R L s)
      (a.interpret M r.coefficients * b.interpret M r.coefficients) :=
    ywl_bind (product_check_ywl hR L r ha hb) fun v hv hvi => hvi ▸ ywl_check R L r hv
  unfold PolynomialRing.multiply
  split
  · exact ywl_checkDegree L _ h
  · exact h

/-- The loop of a power from a canonical `s` that denotes `Aʲ`, over binary
digits, each squaring and, for a digit `1`, multiplying by `a`, which denotes
`A`, is within the limits and denotes `A` to the power that the digits give
when read after `j`. -/
public theorem power_loop_ywl (hR : ExactRing R M) (L : Limits) (r : PolynomialRing P)
    {a : Poly E} (ha : a.Canonical M r.coefficients) :
    ∀ (ds : List Bool) (s : Poly E) (j : ℕ), s.Canonical M r.coefficients →
      s.interpret M r.coefficients = a.interpret M r.coefficients ^ j →
      YieldsWithinLimits M r.coefficients
        (ds.foldlM (init := s) fun s digit => do
          let s ← r.multiply R L s s
          if digit then r.multiply R L s a else pure s)
        (a.interpret M r.coefficients ^ ds.foldl (fun m b => 2 * m + b.toNat) j) := by
  intro ds
  induction ds with
  | nil => exact fun s j hs hsj => ywl_of_yields ⟨s, rfl, hs, by simpa using hsj⟩
  | cons b ds ih =>
    intro s j hs hsj
    simp only [List.foldlM_cons, List.foldl_cons, bind_eq_bind, bind_bind]
    refine ywl_bind (multiply_ywl hR L r hs hs) fun v hv hvi => ?_
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, pure_eq_value, bind_value]
      exact ih v _ hv (by rw [hvi, hsj, ← pow_add, Bool.toNat_false, add_zero, two_mul])
    | true =>
      simp only [↓reduceIte]
      refine ywl_bind (multiply_ywl hR L r hv ha) fun w hw hwi => ?_
      exact ih w _ hw (by rw [hwi, hvi, hsj, ← pow_add, ← pow_succ, Bool.toNat_true, two_mul])

/-- `power` of a canonical polynomial is within the limits and denotes the
power. -/
public theorem power_ywl (hR : ExactRing R M) (L : Limits) (r : PolynomialRing P) {a : Poly E}
    (ha : a.Canonical M r.coefficients) (k : ℕ) :
    YieldsWithinLimits M r.coefficients (r.power R L a k) (a.interpret M r.coefficients ^ k) := by
  unfold PolynomialRing.power
  refine ywl_checkDegree L k (ywl_checkDegree L _ ?_)
  split
  · rename_i hk
    subst hk
    rw [pow_zero]
    exact one_ywl hR L r
  · rename_i hk
    obtain ⟨ds, hds, hval⟩ := binaryDigits_of_pos (Nat.pos_of_ne_zero hk)
    rw [hds, List.tail_cons]
    refine ywl_bind (power_loop_ywl hR L r ha ds a 1 ha (pow_one _).symm) fun v hv hvi => ?_
    rw [hval] at hvi
    exact hvi ▸ ywl_check R L r hv

/-- The power by `0` is the polynomial one, for every polynomial. -/
public theorem power_zero_exponent (L : Limits) (r : PolynomialRing P) (a : Poly E) :
    r.power R L a 0 = r.one R L := by
  simp [PolynomialRing.power, checkDegree]

/-- The loop of a power of the zero polynomial ends in the check of the zero
polynomial. -/
private theorem power_loop_zero (L : Limits) (r : PolynomialRing P) :
    ∀ ds : List Bool,
      (ds.foldlM (init := (Poly.zero : Poly E)) fun (s : Poly E) (digit : Bool) => do
          let s ← r.multiply R L s s
          if digit then r.multiply R L s Poly.zero else pure s).bind
        (fun s => r.check R L s) = r.check R L Poly.zero := by
  have hmul : r.multiply R L (Poly.zero : Poly E) Poly.zero = r.check R L Poly.zero := by
    simp [PolynomialRing.multiply, Poly.degree, Poly.zero, Poly.product, Poly.rows]
  intro ds
  induction ds with
  | nil => rfl
  | cons b ds ih =>
    rw [List.foldlM_cons]
    simp only [bind_eq_bind, bind_bind, hmul]
    rcases check_eq R L r (Poly.zero : Poly E) with h | h | h | h <;> rw [h] <;> rw [h] at ih
    · cases b <;> simp only [bind_value, ↓reduceIte, hmul, h, pure_eq_value,
        Bool.false_eq_true] <;> exact ih
    all_goals rfl

/-- A positive power of the zero polynomial within the bound on exponents is
the checked zero polynomial. -/
public theorem power_zero_base (L : Limits) (r : PolynomialRing P) {k : ℕ} (hk1 : 1 ≤ k)
    (hk2 : k ≤ exponentBound L.maxExponent) :
    r.power R L Poly.zero k = r.zero R L := by
  unfold PolynomialRing.power
  rw [checkDegree_of_le L hk2]
  rw [show (Poly.zero : Poly E).degree.getD 0 = 0 from rfl, Nat.mul_zero,
    checkDegree_of_le L (Nat.zero_le _)]
  simp only [show k ≠ 0 by omega, ↓reduceIte, bind_eq_bind]
  exact power_loop_zero L r _

end Ring

end Kalyx.Proofs.Polynomials.Checks
