module

public import Kalyx.Statements.Polynomials

/-!
# Canonical polynomials: results, coefficients, uniqueness and degrees

An unregistered helper module of the proofs about the univariate polynomials;
it proves no registered statement. It holds what the other proofs share about
results and canonical polynomials:

* `PolyResult` as a lawful monad, with the `simp` lemmas of `bind` and `pure`;
* the interpretation of a list of terms, term by term, and the canonical form
  of a list read through its terms (`canonical_iff`, `canonical_cons_iff`,
  `canonical_append_iff`);
* the coefficients of the interpretation of a canonical polynomial: the
  interpretation of the coefficient of a stored degree, and zero at every
  other degree (`coeff_interpret_of_mem`, `coeff_interpret_of_forall_ne`);
* uniqueness: two canonical polynomials over one parent with the same
  interpretation are equal (`eq_of_interpret_eq`), and so are two results
  that yield them (`eq_of_yields`);
* the degree and the leading coefficient of the representation, those of the
  last term, as Mathlib's `degree`, `natDegree` and `leadingCoeff` of the
  interpretation; the interpretation is zero exactly when there is no term.
-/

namespace Kalyx.Proofs.Polynomials.Canonical

open Kalyx.Spec.Fields Kalyx.Spec.Polynomials Polynomial

/-! ## Results -/

section Results

variable {α β : Type}

/-- `PolyResult` is a lawful monad. -/
public instance instLawfulMonadPolyResult : LawfulMonad PolyResult := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x _ _ => by cases x <;> rfl)
  (seqLeft_eq := fun x y => by cases x <;> cases y <;> rfl)
  (seqRight_eq := fun x y => by cases x <;> cases y <;> rfl)
  (bind_pure_comp := fun _ x => by cases x <;> rfl)
  (bind_map := fun f x => by cases f <;> cases x <;> rfl)

/-- `bind` of the monad is `PolyResult.bind`. -/
@[simp] public theorem bind_eq_bind (x : PolyResult α) (f : α → PolyResult β) :
    (x >>= f) = x.bind f := rfl
/-- `pure` is a value. -/
@[simp] public theorem pure_eq_value (v : α) : (pure v : PolyResult α) = .value v := rfl
/-- A value is passed on by `bind`. -/
@[simp] public theorem bind_value (v : α) (f : α → PolyResult β) :
    (PolyResult.value v).bind f = f v := rfl
/-- A fault stops `bind`. -/
@[simp] public theorem bind_fault (e : PolyFault) (f : α → PolyResult β) :
    (PolyResult.fault e : PolyResult α).bind f = .fault e := rfl
/-- A limit stops `bind`. -/
@[simp] public theorem bind_limit (l : LimitField) (f : α → PolyResult β) :
    (PolyResult.resourceLimit l : PolyResult α).bind f = .resourceLimit l := rfl
/-- `bind` with `value` keeps the result. -/
@[simp] public theorem bind_value_right (x : PolyResult α) : x.bind PolyResult.value = x := by
  cases x <;> rfl
/-- `bind` is associative. -/
@[simp] public theorem bind_bind {γ : Type} (x : PolyResult α) (f : α → PolyResult β)
    (g : β → PolyResult γ) : (x.bind f).bind g = x.bind fun a => (f a).bind g := by
  cases x <;> rfl
/-- A value of an outcome is a value. -/
@[simp] public theorem ofOutcome_value (v : α) :
    PolyResult.ofOutcome (Outcome.value v) = .value v := rfl
/-- A `bind` that returns a value: the first result is a value. -/
public theorem bind_eq_value {x : PolyResult α} {f : α → PolyResult β} {v : β} :
    x.bind f = .value v ↔ ∃ a, x = .value a ∧ f a = .value v := by
  cases x <;> simp

end Results

variable {P E : Type} {K : P → Type} [∀ p, CommRing (K p)] (M : Model P E K) (p : P)

/-! ## Interpretations of lists of terms -/

/-- A polynomial is the polynomial of its terms. -/
@[simp] public theorem mk_terms (a : Poly E) : (⟨a.terms⟩ : Poly E) = a := rfl

/-- The interpretation of the empty list is zero. -/
@[simp] public theorem interpret_nil : (⟨[]⟩ : Poly E).interpret M p = 0 := by
  simp [Poly.interpret]

/-- The interpretation of the zero polynomial is zero. -/
@[simp] public theorem interpret_zero : (Poly.zero : Poly E).interpret M p = 0 := by
  simp [Poly.interpret, Poly.zero]

/-- The interpretation of a list with a first term. -/
public theorem interpret_cons (t : ℕ × E) (l : List (ℕ × E)) :
    (⟨t :: l⟩ : Poly E).interpret M p =
      monomial t.1 ((M p).interpret t.2) + (⟨l⟩ : Poly E).interpret M p := by
  simp [Poly.interpret]

/-- The interpretation of two lists one after the other. -/
public theorem interpret_append (l₁ l₂ : List (ℕ × E)) :
    (⟨l₁ ++ l₂⟩ : Poly E).interpret M p =
      (⟨l₁⟩ : Poly E).interpret M p + (⟨l₂⟩ : Poly E).interpret M p := by
  simp [Poly.interpret]

/-- The interpretation of a list with a last term. -/
public theorem interpret_append_single (l : List (ℕ × E)) (d : ℕ) (c : E) :
    (⟨l ++ [(d, c)]⟩ : Poly E).interpret M p =
      (⟨l⟩ : Poly E).interpret M p + monomial d ((M p).interpret c) := by
  rw [interpret_append, interpret_cons, interpret_nil, add_zero]

/-! ## Canonical lists -/

/-- The canonical form read through the terms: the degrees increase, and each
coefficient is canonical and does not denote zero. -/
public theorem canonical_iff (a : Poly E) :
    a.Canonical M p ↔ a.terms.Pairwise (fun x y => x.1 < y.1) ∧
      ∀ x ∈ a.terms, (M p).canonical x.2 ∧ (M p).interpret x.2 ≠ 0 := by
  simp only [Poly.Canonical, Poly.degrees, Poly.coefficients, List.pairwise_map,
    List.forall_mem_map]

/-- The empty list is canonical. -/
public theorem canonical_nil : (⟨[]⟩ : Poly E).Canonical M p := by
  simp [canonical_iff]

/-- The zero polynomial is canonical. -/
public theorem canonical_zero : (Poly.zero : Poly E).Canonical M p := canonical_nil M p

/-- A list with a first term is canonical when the term lies below the rest,
its coefficient is canonical and not zero, and the rest is canonical. -/
public theorem canonical_cons_iff (t : ℕ × E) (l : List (ℕ × E)) :
    (⟨t :: l⟩ : Poly E).Canonical M p ↔
      (∀ x ∈ l, t.1 < x.1) ∧ ((M p).canonical t.2 ∧ (M p).interpret t.2 ≠ 0) ∧
        (⟨l⟩ : Poly E).Canonical M p := by
  simp only [canonical_iff, List.pairwise_cons, List.forall_mem_cons]
  tauto

/-- A list with a last term is canonical when the rest is canonical and lies
below the term, whose coefficient is canonical and not zero. -/
public theorem canonical_append_iff (l : List (ℕ × E)) (d : ℕ) (c : E) :
    (⟨l ++ [(d, c)]⟩ : Poly E).Canonical M p ↔
      (⟨l⟩ : Poly E).Canonical M p ∧ (∀ x ∈ l, x.1 < d) ∧
        (M p).canonical c ∧ (M p).interpret c ≠ 0 := by
  simp only [canonical_iff, List.pairwise_append, List.pairwise_singleton, List.mem_singleton,
    forall_eq, List.forall_mem_append, true_and]
  tauto

/-- The terms of a canonical list after its first term are canonical. -/
public theorem canonical_tail {t : ℕ × E} {l : List (ℕ × E)}
    (h : (⟨t :: l⟩ : Poly E).Canonical M p) : (⟨l⟩ : Poly E).Canonical M p :=
  ((canonical_cons_iff M p t l).1 h).2.2

/-! ## Coefficients -/

/-- A degree that no term has is a zero coefficient of the interpretation. -/
public theorem coeff_interpret_of_forall_ne (l : List (ℕ × E)) (n : ℕ)
    (h : ∀ x ∈ l, x.1 ≠ n) : ((⟨l⟩ : Poly E).interpret M p).coeff n = 0 := by
  induction l with
  | nil => simp
  | cons t l ih =>
    have ht : t.1 ≠ n := h t List.mem_cons_self
    rw [interpret_cons, coeff_add, coeff_monomial, ih fun x hx => h x (List.mem_cons_of_mem _ hx)]
    simp [ht]

/-- A degree that is not among the degrees is a zero coefficient. -/
public theorem coeff_interpret_of_not_mem (a : Poly E) (n : ℕ) (h : n ∉ a.degrees) :
    (a.interpret M p).coeff n = 0 :=
  coeff_interpret_of_forall_ne M p a.terms n fun x hx hn =>
    h (List.mem_map.2 ⟨x, hx, hn⟩)

/-- The coefficient of the interpretation of a canonical polynomial at a
stored degree is the interpretation of the stored coefficient. -/
public theorem coeff_interpret_of_mem {a : Poly E} (ha : a.Canonical M p) {d : ℕ} {c : E}
    (h : (d, c) ∈ a.terms) : (a.interpret M p).coeff d = (M p).interpret c := by
  obtain ⟨l⟩ := a
  induction l with
  | nil => simp at h
  | cons t l ih =>
    obtain ⟨hlt, -, hl⟩ := (canonical_cons_iff M p t l).1 ha
    rw [interpret_cons, coeff_add, coeff_monomial]
    rcases List.mem_cons.1 h with rfl | h
    · rw [coeff_interpret_of_forall_ne M p l _ fun x hx => (hlt x hx).ne']
      simp
    · rw [ih hl h]
      simp [(hlt _ h).ne]

/-! ## Uniqueness -/

/-- A canonical list with a term does not denote zero. -/
public theorem interpret_cons_ne_zero {t : ℕ × E} {l : List (ℕ × E)}
    (h : (⟨t :: l⟩ : Poly E).Canonical M p) : (⟨t :: l⟩ : Poly E).interpret M p ≠ 0 := by
  intro h0
  have := coeff_interpret_of_mem M p h (d := t.1) (c := t.2) List.mem_cons_self
  rw [h0, coeff_zero] at this
  exact ((canonical_cons_iff M p t l).1 h).2.1.2 this.symm

/-- Canonical forms are unique: two canonical polynomials over one parent that
denote the same polynomial are equal, when the canonical elements of the
parent are unique. -/
public theorem eq_of_interpret_eq (hu : (M p).Unique) {a b : Poly E} (ha : a.Canonical M p)
    (hb : b.Canonical M p) (h : a.interpret M p = b.interpret M p) : a = b := by
  obtain ⟨l₁⟩ := a
  obtain ⟨l₂⟩ := b
  congr 1
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons t l => exact absurd (by rw [← h]; simp) (interpret_cons_ne_zero M p hb)
  | cons t₁ l₁ ih =>
    cases l₂ with
    | nil => exact absurd (by rw [h]; simp) (interpret_cons_ne_zero M p ha)
    | cons t₂ l₂ =>
      obtain ⟨hlt₁, ⟨hc₁, hn₁⟩, hl₁⟩ := (canonical_cons_iff M p t₁ l₁).1 ha
      obtain ⟨hlt₂, ⟨hc₂, hn₂⟩, hl₂⟩ := (canonical_cons_iff M p t₂ l₂).1 hb
      have below : ∀ (t : ℕ × E) (l : List (ℕ × E)), (∀ x ∈ l, t.1 < x.1) → ∀ n, n < t.1 →
          ((⟨t :: l⟩ : Poly E).interpret M p).coeff n = 0 := by
        intro t l hlt n hn
        refine coeff_interpret_of_forall_ne M p _ n fun x hx => ?_
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hn.ne'
        · exact (lt_trans hn (hlt x hx)).ne'
      have hd : t₁.1 = t₂.1 := by
        rcases lt_trichotomy t₁.1 t₂.1 with hlt | heq | hgt
        · have e := congrArg (fun q => q.coeff t₁.1) h
          rw [coeff_interpret_of_mem M p ha List.mem_cons_self, below t₂ l₂ hlt₂ _ hlt] at e
          exact absurd e hn₁
        · exact heq
        · have e := congrArg (fun q => q.coeff t₂.1) h
          rw [coeff_interpret_of_mem M p hb List.mem_cons_self, below t₁ l₁ hlt₁ _ hgt] at e
          exact absurd e.symm hn₂
      have hc : t₁.2 = t₂.2 := by
        apply hu _ _ hc₁ hc₂
        have e := congrArg (fun q => q.coeff t₁.1) h
        rw [coeff_interpret_of_mem M p ha List.mem_cons_self, hd,
          coeff_interpret_of_mem M p hb List.mem_cons_self] at e
        exact e
      have ht : t₁ = t₂ := Prod.ext hd hc
      subst ht
      rw [interpret_cons, interpret_cons] at h
      rw [ih hl₁ l₂ hl₂ (add_left_cancel h)]

/-- Two results that are canonical polynomials with one interpretation are
equal, when the canonical elements of the parent are unique. -/
public theorem eq_of_yields (hu : (M p).Unique) {o o' : PolyResult (Poly E)}
    {x : Polynomial (K p)} (h : Poly.Yields M p o x) (h' : Poly.Yields M p o' x) : o = o' := by
  obtain ⟨a, rfl, ha, hax⟩ := h
  obtain ⟨b, rfl, hb, hbx⟩ := h'
  rw [eq_of_interpret_eq M p hu ha hb (hax.trans hbx.symm)]

/-- A canonical result passed by `bind` to a step that is canonical on each
canonical value that denotes it. -/
public theorem yields_bind {o : PolyResult (Poly E)} {f : Poly E → PolyResult (Poly E)}
    {x y : Polynomial (K p)} (h : Poly.Yields M p o x)
    (hf : ∀ v, v.Canonical M p → v.interpret M p = x → Poly.Yields M p (f v) y) :
    Poly.Yields M p (o.bind f) y := by
  obtain ⟨a, rfl, ha, hax⟩ := h
  exact hf a ha hax

/-! ## Zero and degrees -/

/-- A polynomial is zero exactly when it has no term. -/
public theorem eq_zero_iff (a : Poly E) : a = Poly.zero ↔ a.terms = [] := by
  obtain ⟨l⟩ := a
  simp [Poly.zero]

/-- A canonical polynomial denotes zero exactly when it has no term. -/
public theorem interpret_eq_zero_iff {a : Poly E} (ha : a.Canonical M p) :
    a.interpret M p = 0 ↔ a = Poly.zero := by
  obtain ⟨l⟩ := a
  cases l with
  | nil => simp [Poly.zero]
  | cons t l => simp [Poly.zero, interpret_cons_ne_zero M p ha]

/-- `isZero` is the zero polynomial. -/
public theorem isZero_iff (a : Poly E) : a.isZero = true ↔ a = Poly.zero := by
  rw [eq_zero_iff]
  simp [Poly.isZero]

/-- The degree of the representation is none exactly for the zero
polynomial. -/
public theorem degree_eq_none_iff (a : Poly E) : a.degree = none ↔ a = Poly.zero := by
  rw [eq_zero_iff]
  simp [Poly.degree]

/-- The leading coefficient of the representation is none exactly for the
zero polynomial. -/
public theorem leadingCoefficient_eq_none_iff (a : Poly E) :
    a.leadingCoefficient = none ↔ a = Poly.zero := by
  rw [eq_zero_iff]
  simp [Poly.leadingCoefficient]

/-- The degree and the leading coefficient of the representation, those of
the last term `(d, c)`. -/
public theorem degree_eq_some_iff (a : Poly E) (d : ℕ) :
    a.degree = some d ↔ ∃ c, a.terms.getLast? = some (d, c) := by
  simp [Poly.degree]

/-- Every degree of a canonical polynomial is at most the degree of its last
term. -/
public theorem le_of_getLast? {a : Poly E} (ha : a.Canonical M p) {d : ℕ} {c : E}
    (h : a.terms.getLast? = some (d, c)) : ∀ x ∈ a.terms, x.1 ≤ d := by
  obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.1 h
  have ha' := ha
  obtain ⟨l'⟩ := a
  simp only at hl
  subst hl
  obtain ⟨-, hlt, -⟩ := (canonical_append_iff M p l d c).1 ha'
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact (hlt x hx).le
  · simp at hx
    rw [hx]

/-- The interpretation of a canonical polynomial whose last term is `(d, c)`
has the degree `d` and the leading coefficient that `c` denotes. -/
public theorem degree_interpret_of_getLast? {a : Poly E} (ha : a.Canonical M p) {d : ℕ}
    {c : E} (h : a.terms.getLast? = some (d, c)) :
    (a.interpret M p).degree = d ∧ (a.interpret M p).natDegree = d ∧
      (a.interpret M p).leadingCoeff = (M p).interpret c := by
  have hmem : (d, c) ∈ a.terms := List.mem_of_getLast? h
  have hle := le_of_getLast? M p ha h
  have hc : (a.interpret M p).coeff d = (M p).interpret c := coeff_interpret_of_mem M p ha hmem
  have hc0 : (M p).interpret c ≠ 0 := ((canonical_iff M p a).1 ha).2 _ hmem |>.2
  have hdeg : (a.interpret M p).degree = d := by
    refine degree_eq_of_le_of_coeff_ne_zero ?_ (by rw [hc]; exact hc0)
    rw [degree_le_iff_coeff_zero]
    intro m hm
    have hm' : d < m := by exact_mod_cast hm
    exact coeff_interpret_of_forall_ne M p a.terms m fun x hx => by
      have := hle x hx
      omega
  have hnat : (a.interpret M p).natDegree = d := natDegree_eq_of_degree_eq_some hdeg
  refine ⟨hdeg, hnat, ?_⟩
  rw [leadingCoeff, hnat, hc]

/-- The degree of the interpretation of a canonical polynomial is the degree
of the representation, `⊥` for the zero polynomial. -/
public theorem degree_interpret {a : Poly E} (ha : a.Canonical M p) :
    (a.interpret M p).degree = (a.degree : WithBot ℕ) := by
  cases h : a.terms.getLast? with
  | none =>
    have hd : a.degree = none := by simp [Poly.degree, h]
    rw [hd, (degree_eq_none_iff a).1 hd, interpret_zero, degree_zero]
    rfl
  | some t =>
    obtain ⟨d, c⟩ := t
    have hd : a.degree = some d := by simp [Poly.degree, h]
    rw [(degree_interpret_of_getLast? M p ha h).1, hd]
    rfl

/-- The natural degree of the interpretation of a canonical polynomial is the
degree of the representation, `0` for the zero polynomial. -/
public theorem natDegree_interpret {a : Poly E} (ha : a.Canonical M p) :
    (a.interpret M p).natDegree = a.degree.getD 0 := by
  cases h : a.terms.getLast? with
  | none =>
    have h0 : a = Poly.zero := (degree_eq_none_iff a).1 (by simp [Poly.degree, h])
    subst h0
    simp [Poly.degree, Poly.zero]
  | some t =>
    obtain ⟨d, c⟩ := t
    rw [(degree_interpret_of_getLast? M p ha h).2.1]
    simp [Poly.degree, h]

/-- The leading coefficient of the interpretation of a canonical polynomial is
the interpretation of the leading coefficient of the representation, `0` for
the zero polynomial. -/
public theorem leadingCoeff_interpret {a : Poly E} (ha : a.Canonical M p) :
    (a.interpret M p).leadingCoeff = (a.leadingCoefficient.map (M p).interpret).getD 0 := by
  cases h : a.terms.getLast? with
  | none =>
    have h0 : a = Poly.zero := (degree_eq_none_iff a).1 (by simp [Poly.degree, h])
    subst h0
    simp [Poly.leadingCoefficient, Poly.zero]
  | some t =>
    obtain ⟨d, c⟩ := t
    rw [(degree_interpret_of_getLast? M p ha h).2.2]
    simp [Poly.leadingCoefficient, h]

/-- The terms of a canonical polynomial all lie below `n` exactly when the
degree of its interpretation does. -/
public theorem forall_lt_iff_degree_lt {a : Poly E} (ha : a.Canonical M p) (n : ℕ) :
    (∀ x ∈ a.terms, x.1 < n) ↔ (a.interpret M p).degree < n := by
  cases h : a.terms.getLast? with
  | none =>
    have h0 : a = Poly.zero := (degree_eq_none_iff a).1 (by simp [Poly.degree, h])
    subst h0
    simp [Poly.zero]
  | some t =>
    obtain ⟨d, c⟩ := t
    rw [(degree_interpret_of_getLast? M p ha h).1, Nat.cast_lt]
    constructor
    · exact fun hall => hall _ (List.mem_of_getLast? h)
    · exact fun hd x hx => lt_of_le_of_lt (le_of_getLast? M p ha h x hx) hd

end Kalyx.Proofs.Polynomials.Canonical
