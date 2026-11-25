module

public import Kalyx.Proofs.Polynomials.Canonical

/-!
# The writer and the operations without the checks

An unregistered helper module of the proofs about the univariate polynomials;
it proves no registered statement. Over a coefficient ring that is exact under
an interpretation (`ExactRing`), on canonical operands:

* the zero test answers by the interpretation (`testZero_of_eq_zero`,
  `testZero_of_ne_zero`); the writer appends a term above the last degree
  and never reports `Internal` there (`append_of_lt`, `append_spec`), and a
  term written after its zero test is dropped exactly when its coefficient
  denotes zero (`appendNonzero_spec`), so `Poly.monomial` denotes the monomial
  (`monomial_spec`);
* each loop over terms keeps its invariant: the accumulated polynomial is
  canonical, lies below the degrees still to be written, and denotes the
  partial result (`appendEach_spec`, `mergeStep_spec`, `merge_spec`,
  `row_spec`, `rows_spec`, `derivativeTerms_spec`);
* so the negation, the sum, the difference, the product and the derivative
  without the checks return canonical polynomials that denote the operations
  of Mathlib's `Polynomial` (`negate_spec`, `sum_spec`, `difference_spec`,
  `product_spec`, `derivative_spec`), and so does the product with a
  constant (`scale_spec`).
-/

namespace Kalyx.Proofs.Polynomials.Operations

open Kalyx.Spec.Fields Kalyx.Spec.Polynomials Kalyx.Statements.Polynomials Polynomial
open Kalyx.Proofs.Polynomials.Canonical

variable {P E : Type} {K : P → Type} [∀ p, CommRing (K p)] {R : CoefficientRing P E Empty}
  {M : Model P E K} {p : P}

/-! ## The zero test and the writer -/

/-- The zero test of a canonical coefficient that denotes zero answers
`true`. -/
public theorem testZero_of_eq_zero (hz : ZeroTestExact R M) {c : E} (hc : (M p).canonical c)
    (h : (M p).interpret c = 0) : testZero R p c = .value true := by
  unfold testZero
  rw [(hz.zero p c hc).2 h]
  rfl

/-- The zero test of a canonical coefficient that does not denote zero
answers `false`. -/
public theorem testZero_of_ne_zero (hz : ZeroTestExact R M) {c : E} (hc : (M p).canonical c)
    (h : (M p).interpret c ≠ 0) : testZero R p c = .value false := by
  unfold testZero
  rw [(hz.nonzero p c hc).2 h]
  rfl

/-- The writer appends a term above every degree. -/
public theorem append_of_lt {a : Poly E} {d : ℕ} (c : E) (h : ∀ x ∈ a.terms, x.1 < d) :
    a.append d c = .value ⟨a.terms ++ [(d, c)]⟩ := by
  have hall : a.degree.all (· < d) = true := by
    cases hl : a.terms.getLast? with
    | none => simp [Poly.degree, hl]
    | some t => simp [Poly.degree, hl, h t (List.mem_of_getLast? hl)]
  simp [Poly.append, hall]

/-- The writer on a canonical polynomial with a term above its degrees, whose
coefficient is canonical and not zero: a canonical polynomial that denotes
the sum with the monomial, whose degrees are at most that of the term. -/
public theorem append_spec {a : Poly E} (ha : a.Canonical M p) {d : ℕ} {c : E}
    (h : ∀ x ∈ a.terms, x.1 < d) (hc : (M p).canonical c) (hc0 : (M p).interpret c ≠ 0) :
    ∃ b, a.append d c = .value b ∧ b.Canonical M p ∧
      b.interpret M p = a.interpret M p + monomial d ((M p).interpret c) ∧
        ∀ x ∈ b.terms, x.1 ≤ d := by
  refine ⟨⟨a.terms ++ [(d, c)]⟩, append_of_lt c h,
    (canonical_append_iff M p a.terms d c).2 ⟨ha, h, hc, hc0⟩,
    interpret_append_single M p a.terms d c, fun x hx => ?_⟩
  rcases List.mem_append.1 hx with hx | hx
  · exact (h x hx).le
  · simp at hx
    rw [hx]

/-- A term whose coefficient denotes zero is not written. -/
public theorem appendNonzero_of_eq_zero (hz : ZeroTestExact R M) (a : Poly E) (d : ℕ) {c : E}
    (hc : (M p).canonical c) (h0 : (M p).interpret c = 0) :
    a.appendNonzero R p d c = .value a := by
  simp [Poly.appendNonzero, testZero_of_eq_zero hz hc h0]

/-- A term whose coefficient does not denote zero is written by the writer. -/
public theorem appendNonzero_of_ne_zero (hz : ZeroTestExact R M) (a : Poly E) (d : ℕ) {c : E}
    (hc : (M p).canonical c) (h0 : (M p).interpret c ≠ 0) :
    a.appendNonzero R p d c = a.append d c := by
  simp [Poly.appendNonzero, testZero_of_ne_zero hz hc h0]

/-- A term written after its zero test above the degrees of a canonical
polynomial: a canonical polynomial that denotes the sum with the monomial,
whose degrees are at most that of the term. -/
public theorem appendNonzero_spec (hz : ZeroTestExact R M) {a : Poly E} (ha : a.Canonical M p)
    {d : ℕ} {c : E} (h : ∀ x ∈ a.terms, x.1 < d) (hc : (M p).canonical c) :
    ∃ b, a.appendNonzero R p d c = .value b ∧ b.Canonical M p ∧
      b.interpret M p = a.interpret M p + monomial d ((M p).interpret c) ∧
        ∀ x ∈ b.terms, x.1 ≤ d := by
  by_cases h0 : (M p).interpret c = 0
  · exact ⟨a, appendNonzero_of_eq_zero hz a d hc h0, ha, by simp [h0], fun x hx => (h x hx).le⟩
  · rw [appendNonzero_of_ne_zero hz a d hc h0]
    exact append_spec ha h hc h0

/-- `Poly.monomial` of a canonical coefficient denotes the monomial. -/
public theorem monomial_spec (hz : ZeroTestExact R M) (d : ℕ) {c : E} (hc : (M p).canonical c) :
    Poly.Yields M p (Poly.monomial R p d c) (monomial d ((M p).interpret c)) := by
  obtain ⟨b, hb, hbc, hbi, -⟩ :=
    appendNonzero_spec (R := R) hz (canonical_zero M p) (d := d) (by simp [Poly.zero]) hc
  exact ⟨b, hb, hbc, by rw [hbi, interpret_zero, zero_add]⟩

/-! ## Loops over terms -/

/-- The terms of a canonical list, each with its coefficient mapped by `f`,
which multiplies the interpretation by the unit `s`, written above a
canonical polynomial below them: a canonical polynomial that denotes the
polynomial plus `s` times the list. -/
public theorem appendEach_spec {f : E → Outcome E} {s : K p} (hs : IsUnit s)
    (hf : ∀ c, (M p).canonical c → M.Yields p (f c) (s * (M p).interpret c)) :
    ∀ (l : List (ℕ × E)) (acc : Poly E), acc.Canonical M p → (⟨l⟩ : Poly E).Canonical M p →
      (∀ x ∈ acc.terms, ∀ y ∈ l, x.1 < y.1) →
      ∃ b, acc.appendEach f l = .value b ∧ b.Canonical M p ∧
        b.interpret M p = acc.interpret M p + C s * (⟨l⟩ : Poly E).interpret M p := by
  intro l
  induction l with
  | nil => exact fun acc hacc _ _ => ⟨acc, rfl, hacc, by simp⟩
  | cons t l ih =>
    intro acc hacc hl hbelow
    obtain ⟨d, c⟩ := t
    obtain ⟨hlt, ⟨hc, hc0⟩, hl'⟩ := (canonical_cons_iff M p (d, c) l).1 hl
    obtain ⟨c', hfc, hc', hic'⟩ := hf c hc
    have hc'0 : (M p).interpret c' ≠ 0 := by
      rw [hic']
      exact fun h => hc0 (hs.mul_right_eq_zero.1 h)
    obtain ⟨b, hb, hbc, hbi, hble⟩ :=
      append_spec hacc (fun x hx => hbelow x hx _ List.mem_cons_self) hc' hc'0
    obtain ⟨b', hb', hb'c, hb'i⟩ :=
      ih b hbc hl' fun x hx y hy => lt_of_le_of_lt (hble x hx) (hlt y hy)
    refine ⟨b', ?_, hb'c, ?_⟩
    · simp only [Poly.appendEach, hfc, bind_eq_bind, ofOutcome_value, bind_value, hb, hb']
    · rw [hb'i, hbi, hic', interpret_cons, mul_add, C_mul_monomial]
      ring

section Merge

variable {combine : E → E → Outcome E} {alone : E → Outcome E} {s : K p}

/-- One step of a merge, for a first term `c x^d` of the left operand below
its other terms `as`, whose merge `rest` keeps the invariant: a canonical
polynomial that denotes the accumulated polynomial, the term, `as`, and `s`
times the right operand. The coefficients of one degree are combined into
their sum with `s` times the right one, and a term of the right operand alone
is multiplied by the unit `s`. -/
public theorem mergeStep_spec (hz : ZeroTestExact R M) (hs : IsUnit s)
    (hcomb : ∀ c c', (M p).canonical c → (M p).canonical c' →
      M.Yields p (combine c c') ((M p).interpret c + s * (M p).interpret c'))
    (halone : ∀ c, (M p).canonical c → M.Yields p (alone c) (s * (M p).interpret c))
    {as : List (ℕ × E)} {rest : Poly E → List (ℕ × E) → PolyResult (Poly E)}
    (hrest : ∀ acc bs, acc.Canonical M p → (⟨bs⟩ : Poly E).Canonical M p →
      (∀ x ∈ acc.terms, (∀ y ∈ as, x.1 < y.1) ∧ ∀ y ∈ bs, x.1 < y.1) →
      ∃ b, rest acc bs = .value b ∧ b.Canonical M p ∧
        b.interpret M p = acc.interpret M p + (⟨as⟩ : Poly E).interpret M p +
          C s * (⟨bs⟩ : Poly E).interpret M p)
    {d : ℕ} {c : E} (hc : (M p).canonical c) (hc0 : (M p).interpret c ≠ 0)
    (hd : ∀ y ∈ as, d < y.1) :
    ∀ (bs : List (ℕ × E)) (acc : Poly E), acc.Canonical M p → (⟨bs⟩ : Poly E).Canonical M p →
      (∀ x ∈ acc.terms, x.1 < d ∧ (∀ y ∈ as, x.1 < y.1) ∧ ∀ y ∈ bs, x.1 < y.1) →
      ∃ b, Poly.mergeStep R p combine alone d c rest acc bs = .value b ∧ b.Canonical M p ∧
        b.interpret M p = acc.interpret M p + monomial d ((M p).interpret c) +
          (⟨as⟩ : Poly E).interpret M p + C s * (⟨bs⟩ : Poly E).interpret M p := by
  intro bs
  induction bs with
  | nil =>
    intro acc hacc _ hbelow
    obtain ⟨b, hb, hbc, hbi, hble⟩ := append_spec hacc (fun x hx => (hbelow x hx).1) hc hc0
    obtain ⟨b', hb', hb'c, hb'i⟩ := hrest b [] hbc (canonical_nil M p)
      fun x hx => ⟨fun y hy => lt_of_le_of_lt (hble x hx) (hd y hy), by simp⟩
    refine ⟨b', ?_, hb'c, ?_⟩
    · simp only [Poly.mergeStep, bind_eq_bind, hb, bind_value, hb']
    · rw [hb'i, hbi]
  | cons t bs ih =>
    intro acc hacc hbs hbelow
    obtain ⟨e, c'⟩ := t
    obtain ⟨hlt, ⟨hc', hc'0⟩, hbs'⟩ := (canonical_cons_iff M p (e, c') bs).1 hbs
    rcases lt_trichotomy d e with hde | rfl | hed
    · obtain ⟨b, hb, hbc, hbi, hble⟩ := append_spec hacc (fun x hx => (hbelow x hx).1) hc hc0
      obtain ⟨b', hb', hb'c, hb'i⟩ := hrest b ((e, c') :: bs) hbc hbs fun x hx =>
        ⟨fun y hy => lt_of_le_of_lt (hble x hx) (hd y hy), fun y hy => by
          rcases List.mem_cons.1 hy with rfl | hy
          · exact lt_of_le_of_lt (hble x hx) hde
          · exact lt_of_le_of_lt (hble x hx) (lt_trans hde (hlt y hy))⟩
      refine ⟨b', ?_, hb'c, ?_⟩
      · simp only [Poly.mergeStep, hde, ↓reduceIte, bind_eq_bind, hb, bind_value, hb']
      · rw [hb'i, hbi]
    · obtain ⟨m, hm, hmc, hmi⟩ := hcomb c c' hc hc'
      obtain ⟨b, hb, hbc, hbi, hble⟩ :=
        appendNonzero_spec hz hacc (fun x hx => (hbelow x hx).1) hmc
      obtain ⟨b', hb', hb'c, hb'i⟩ := hrest b bs hbc hbs' fun x hx =>
        ⟨fun y hy => lt_of_le_of_lt (hble x hx) (hd y hy),
          fun y hy => lt_of_le_of_lt (hble x hx) (hlt y hy)⟩
      refine ⟨b', ?_, hb'c, ?_⟩
      · simp only [Poly.mergeStep, lt_irrefl, ↓reduceIte, bind_eq_bind, hm, ofOutcome_value,
          bind_value, hb, hb']
      · rw [hb'i, hbi, hmi, interpret_cons, mul_add, C_mul_monomial]
        simp only [map_add]
        ring
    · obtain ⟨m, hm, hmc, hmi⟩ := halone c' hc'
      have hm0 : (M p).interpret m ≠ 0 := by
        rw [hmi]
        exact fun h => hc'0 (hs.mul_right_eq_zero.1 h)
      obtain ⟨b, hb, hbc, hbi, hble⟩ :=
        append_spec hacc (fun x hx => (hbelow x hx).2.2 _ List.mem_cons_self) hmc hm0
      obtain ⟨b', hb', hb'c, hb'i⟩ := ih b hbc hbs' fun x hx =>
        ⟨lt_of_le_of_lt (hble x hx) hed,
          fun y hy => lt_of_le_of_lt (hble x hx) (lt_trans hed (hd y hy)),
          fun y hy => lt_of_le_of_lt (hble x hx) (hlt y hy)⟩
      refine ⟨b', ?_, hb'c, ?_⟩
      · simp only [Poly.mergeStep, not_lt_of_gt hed, hed, ↓reduceIte, bind_eq_bind, hm,
          ofOutcome_value, bind_value, hb, hb']
      · rw [hb'i, hbi, hmi, interpret_cons, mul_add, C_mul_monomial]
        ring

/-- The merge of two canonical lists above a canonical polynomial below both:
a canonical polynomial that denotes the polynomial, the left list, and `s`
times the right list. -/
public theorem merge_spec (hz : ZeroTestExact R M) (hs : IsUnit s)
    (hcomb : ∀ c c', (M p).canonical c → (M p).canonical c' →
      M.Yields p (combine c c') ((M p).interpret c + s * (M p).interpret c'))
    (halone : ∀ c, (M p).canonical c → M.Yields p (alone c) (s * (M p).interpret c)) :
    ∀ (as : List (ℕ × E)) (acc : Poly E) (bs : List (ℕ × E)), acc.Canonical M p →
      (⟨as⟩ : Poly E).Canonical M p → (⟨bs⟩ : Poly E).Canonical M p →
      (∀ x ∈ acc.terms, (∀ y ∈ as, x.1 < y.1) ∧ ∀ y ∈ bs, x.1 < y.1) →
      ∃ b, Poly.merge R p combine alone as acc bs = .value b ∧ b.Canonical M p ∧
        b.interpret M p = acc.interpret M p + (⟨as⟩ : Poly E).interpret M p +
          C s * (⟨bs⟩ : Poly E).interpret M p := by
  intro as
  induction as with
  | nil =>
    intro acc bs hacc _ hbs hbelow
    obtain ⟨b, hb, hbc, hbi⟩ :=
      appendEach_spec hs halone bs acc hacc hbs fun x hx => (hbelow x hx).2
    exact ⟨b, by simp only [Poly.merge, hb], hbc, by rw [hbi]; simp⟩
  | cons t as ih =>
    intro acc bs hacc has hbs hbelow
    obtain ⟨d, c⟩ := t
    obtain ⟨hlt, ⟨hc, hc0⟩, has'⟩ := (canonical_cons_iff M p (d, c) as).1 has
    obtain ⟨b, hb, hbc, hbi⟩ := mergeStep_spec hz hs hcomb halone
      (rest := Poly.merge R p combine alone as)
      (fun acc bs hacc hbs hbelow => ih acc bs hacc has' hbs hbelow) hc hc0 hlt bs acc hacc hbs
      fun x hx => ⟨(hbelow x hx).1 _ List.mem_cons_self,
        fun y hy => (hbelow x hx).1 y (List.mem_cons_of_mem _ hy), (hbelow x hx).2⟩
    refine ⟨b, by simp only [Poly.merge]; exact hb, hbc, ?_⟩
    rw [hbi, interpret_cons]
    ring

end Merge

/-! ## Negation, sums and differences -/

/-- The negation of a canonical polynomial is canonical and denotes the
negation. -/
public theorem negate_spec (hR : ExactRing R M) {a : Poly E} (ha : a.Canonical M p) :
    Poly.Yields M p (Poly.negate R p a) (-a.interpret M p) := by
  obtain ⟨b, hb, hbc, hbi⟩ := appendEach_spec (f := R.negate p) (s := -1) isUnit_one.neg
    (fun c hc => by rw [neg_one_mul]; exact hR.1.negate p c hc) a.terms Poly.zero
    (canonical_zero M p) ha (by simp [Poly.zero])
  exact ⟨b, hb, hbc, by rw [hbi]; simp⟩

/-- The sum of canonical polynomials is canonical and denotes the sum. -/
public theorem sum_spec (hR : ExactRing R M) {a b : Poly E} (ha : a.Canonical M p)
    (hb : b.Canonical M p) :
    Poly.Yields M p (Poly.sum R p a b) (a.interpret M p + b.interpret M p) := by
  obtain ⟨t, ht, htc, hti⟩ := merge_spec (R := R) (combine := R.add p) (alone := .value)
    (s := 1) hR.2 isUnit_one (fun c c' hc hc' => by rw [one_mul]; exact hR.1.add p c c' hc hc')
    (fun c hc => ⟨c, rfl, hc, by rw [one_mul]⟩) a.terms Poly.zero b.terms (canonical_zero M p)
    ha hb (by simp [Poly.zero])
  exact ⟨t, ht, htc, by rw [hti]; simp⟩

/-- The difference of canonical polynomials is canonical and denotes the
difference. -/
public theorem difference_spec (hR : ExactRing R M) {a b : Poly E} (ha : a.Canonical M p)
    (hb : b.Canonical M p) :
    Poly.Yields M p (Poly.difference R p a b) (a.interpret M p - b.interpret M p) := by
  obtain ⟨t, ht, htc, hti⟩ := merge_spec (R := R) (combine := R.subtract p)
    (alone := R.negate p) (s := -1) hR.2 isUnit_one.neg
    (fun c c' hc hc' => by
      rw [neg_one_mul, ← sub_eq_add_neg]; exact hR.1.subtract p c c' hc hc')
    (fun c hc => by rw [neg_one_mul]; exact hR.1.negate p c hc) a.terms Poly.zero b.terms
    (canonical_zero M p) ha hb (by simp [Poly.zero])
  exact ⟨t, ht, htc, by rw [hti]; simp [sub_eq_add_neg]⟩

/-! ## Products -/

/-- The row `c x^d · q` of a canonical list `q` above a canonical polynomial
below its degrees: a canonical polynomial that denotes the polynomial plus
the row. -/
public theorem row_spec (hR : ExactRing R M) (d : ℕ) {c : E} (hc : (M p).canonical c) :
    ∀ (q : List (ℕ × E)) (acc : Poly E), acc.Canonical M p → (⟨q⟩ : Poly E).Canonical M p →
      (∀ x ∈ acc.terms, ∀ y ∈ q, x.1 < d + y.1) →
      ∃ b, Poly.row R p d c acc q = .value b ∧ b.Canonical M p ∧
        b.interpret M p =
          acc.interpret M p + monomial d ((M p).interpret c) * (⟨q⟩ : Poly E).interpret M p := by
  intro q
  induction q with
  | nil => exact fun acc hacc _ _ => ⟨acc, rfl, hacc, by simp⟩
  | cons t q ih =>
    intro acc hacc hq hbelow
    obtain ⟨e, c'⟩ := t
    obtain ⟨hlt, ⟨hc', -⟩, hq'⟩ := (canonical_cons_iff M p (e, c') q).1 hq
    obtain ⟨m, hm, hmc, hmi⟩ := hR.1.multiply p c c' hc hc'
    obtain ⟨b, hb, hbc, hbi, hble⟩ :=
      appendNonzero_spec hR.2 hacc (fun x hx => hbelow x hx _ List.mem_cons_self) hmc
    obtain ⟨b', hb', hb'c, hb'i⟩ := ih b hbc hq' fun x hx y hy =>
      lt_of_le_of_lt (hble x hx) (Nat.add_lt_add_left (hlt y hy) d)
    refine ⟨b', ?_, hb'c, ?_⟩
    · simp only [Poly.row, hm, bind_eq_bind, ofOutcome_value, bind_value, hb, hb']
    · rw [hb'i, hbi, hmi, interpret_cons, mul_add, monomial_mul_monomial]
      ring

/-- The rows of a canonical list `l` over a canonical list `q` without the
checks, from a canonical total: a canonical polynomial that denotes the total
plus the product of the lists. -/
public theorem rows_spec (hR : ExactRing R M) {q : List (ℕ × E)}
    (hq : (⟨q⟩ : Poly E).Canonical M p) :
    ∀ (l : List (ℕ × E)) (total : Poly E), total.Canonical M p → (⟨l⟩ : Poly E).Canonical M p →
      ∃ b, Poly.rows R p .value q total l = .value b ∧ b.Canonical M p ∧
        b.interpret M p = total.interpret M p +
          (⟨l⟩ : Poly E).interpret M p * (⟨q⟩ : Poly E).interpret M p := by
  intro l
  induction l with
  | nil => exact fun total htotal _ => ⟨total, rfl, htotal, by simp⟩
  | cons t l ih =>
    intro total htotal hl
    obtain ⟨d, c⟩ := t
    obtain ⟨-, ⟨hc, -⟩, hl'⟩ := (canonical_cons_iff M p (d, c) l).1 hl
    obtain ⟨w, hw, hwc, hwi⟩ :=
      row_spec hR d hc q Poly.zero (canonical_zero M p) hq (by simp [Poly.zero])
    obtain ⟨u, hu, huc, hui⟩ := sum_spec hR htotal hwc
    obtain ⟨b, hb, hbc, hbi⟩ := ih u huc hl'
    refine ⟨b, ?_, hbc, ?_⟩
    · simp only [Poly.rows, bind_eq_bind, hw, bind_value, hu, hb]
    · rw [hbi, hui, hwi, interpret_cons, interpret_zero]
      ring

/-- The product without the checks of canonical polynomials is canonical and
denotes the product. -/
public theorem product_spec (hR : ExactRing R M) {a b : Poly E} (ha : a.Canonical M p)
    (hb : b.Canonical M p) :
    Poly.Yields M p (Poly.product R p .value a b) (a.interpret M p * b.interpret M p) := by
  unfold Poly.product
  split
  · obtain ⟨t, ht, htc, hti⟩ := rows_spec (R := R) hR (q := a.terms) ha b.terms Poly.zero
      (canonical_zero M p) hb
    exact ⟨t, ht, htc, by rw [hti]; simp [mul_comm]⟩
  · obtain ⟨t, ht, htc, hti⟩ := rows_spec (R := R) hR (q := b.terms) hb a.terms Poly.zero
      (canonical_zero M p) ha
    exact ⟨t, ht, htc, by rw [hti]; simp⟩

/-- The product of a canonical polynomial with a canonical element
(`Poly.scale`) is canonical and denotes the product with the constant. -/
public theorem scale_spec (hR : ExactRing R M) {u : E} (hu : (M p).canonical u) {a : Poly E}
    (ha : a.Canonical M p) :
    Poly.Yields M p (Poly.scale R p u a) (C ((M p).interpret u) * a.interpret M p) := by
  obtain ⟨b, hb, hbc, hbi⟩ :=
    row_spec hR 0 hu a.terms Poly.zero (canonical_zero M p) ha (by simp [Poly.zero])
  exact ⟨b, hb, hbc, by rw [hbi]; simp⟩

/-! ## The derivative -/

/-- The terms of the derivative of a canonical list above a canonical
polynomial whose degrees lie below those of the derivative: a canonical
polynomial that denotes the polynomial plus the derivative of the list. -/
public theorem derivativeTerms_spec (hR : ExactRing R M) :
    ∀ (l : List (ℕ × E)) (acc : Poly E), acc.Canonical M p → (⟨l⟩ : Poly E).Canonical M p →
      (∀ x ∈ acc.terms, ∀ y ∈ l, x.1 + 1 < y.1) →
      ∃ b, Poly.derivativeTerms R p acc l = .value b ∧ b.Canonical M p ∧
        b.interpret M p = acc.interpret M p + derivative ((⟨l⟩ : Poly E).interpret M p) := by
  intro l
  induction l with
  | nil => exact fun acc hacc _ _ => ⟨acc, rfl, hacc, by simp⟩
  | cons t l ih =>
    intro acc hacc hl hbelow
    obtain ⟨d, c⟩ := t
    obtain ⟨hlt, ⟨hc, -⟩, hl'⟩ := (canonical_cons_iff M p (d, c) l).1 hl
    cases d with
    | zero =>
      obtain ⟨b, hb, hbc, hbi⟩ :=
        ih acc hacc hl' fun x hx y hy => hbelow x hx y (List.mem_cons_of_mem _ hy)
      refine ⟨b, ?_, hbc, ?_⟩
      · simp only [Poly.derivativeTerms, hb]
      · rw [hbi, interpret_cons, derivative_add, monomial_zero_left, derivative_C, zero_add]
    | succ d =>
      obtain ⟨hn, hnI⟩ := hR.1.fromInteger p ((d + 1 : ℕ) : ℤ)
      obtain ⟨m, hm, hmc, hmi⟩ := hR.1.multiply p _ c hn hc
      obtain ⟨b, hb, hbc, hbi, hble⟩ := appendNonzero_spec hR.2 hacc (d := d)
        (fun x hx => by have := hbelow x hx _ List.mem_cons_self; simp at this; omega) hmc
      obtain ⟨b', hb', hb'c, hb'i⟩ := ih b hbc hl' fun x hx y hy => by
        have h1 := hble x hx
        have h2 := hlt y hy
        simp at h2
        omega
      refine ⟨b', ?_, hb'c, ?_⟩
      · simp only [Poly.derivativeTerms, hm, bind_eq_bind, ofOutcome_value, bind_value, hb, hb']
      · rw [hb'i, hbi, hmi, hnI, interpret_cons, derivative_add, derivative_monomial]
        simp only [Nat.add_sub_cancel, Int.cast_natCast]
        rw [mul_comm]
        ring

/-- The derivative without the checks of a canonical polynomial is canonical
and denotes Mathlib's `derivative`. -/
public theorem derivative_spec (hR : ExactRing R M) {a : Poly E} (ha : a.Canonical M p) :
    Poly.Yields M p (Poly.derivative R p a) (derivative (a.interpret M p)) := by
  obtain ⟨b, hb, hbc, hbi⟩ :=
    derivativeTerms_spec (R := R) hR a.terms Poly.zero (canonical_zero M p) ha
      (by simp [Poly.zero])
  exact ⟨b, hb, hbc, by rw [hbi]; simp⟩

end Kalyx.Proofs.Polynomials.Operations
