module

public import Kalyx.Proofs.Multivariate.Orders

/-!
# Canonical multivariate polynomials: uniqueness, completeness and normalization

An unregistered helper module of the proofs about the multivariate
polynomials; it proves no registered statement. It holds what the proofs about
the form of the polynomials and about the ring operations share, over a
coefficient ring that is exact under an interpretation (`ExactRing`):

* the `simp` lemmas of `bind` and `pure` of `MvResult`, and the zero test of a
  canonical coefficient, which answers by its interpretation;
* the strict order and the comparison of a monomial order, read from
  `monomialOrdersAreStrictTotalOrders`;
* the interpretation of a list of terms, term by term, and the canonical form
  read through the terms (`canonical_iff_terms`, `canonical_cons_iff`);
* the coefficients and the support of the interpretation of a canonical
  polynomial (`coeff_interpret_of_mem`, `coeff_interpret_of_forall_ne`,
  `mem_support_interpret_iff`), which is zero exactly when the polynomial has
  no term (`interpret_eq_zero_iff`);
* the canonical form of the polynomials of a ring as the operations need it:
  canonical forms are unique (`unique`, `eq_of_interpret_eq`, `eq_of_yields`),
  a polynomial is canonical exactly when its monomials increase and its
  coefficients are canonical and nonzero by the zero test (`canonical_iff`),
  the zero polynomial denotes zero (`yields_zero`), and a monomial denotes the
  monomial of Mathlib (`monomial_yields`);
* normalization of terms with canonical coefficients gives the canonical form
  of their sum, whatever their order (`normalize_yields`, `normalize_perm`),
  and so every polynomial of Mathlib has a canonical form when every element
  of the coefficient ring has one (`complete`).
-/

namespace Kalyx.Proofs.Multivariate.Canonical

open Kalyx.Spec.Fields Kalyx.Spec.Multivariate Kalyx.Statements.Multivariate MvPolynomial

/-! ## Results -/

section Results

variable {α β : Type}

/-- `bind` of the monad is `MvResult.bind`. -/
@[simp] public theorem bind_eq_bind (x : MvResult α) (f : α → MvResult β) :
    (x >>= f) = x.bind f := rfl

/-- `pure` is a value. -/
@[simp] public theorem pure_eq_value (v : α) : (pure v : MvResult α) = .value v := rfl

/-- A value is passed on by `bind`. -/
@[simp] public theorem bind_value (v : α) (f : α → MvResult β) :
    (MvResult.value v).bind f = f v := rfl

/-- A value of an outcome is a value. -/
@[simp] public theorem ofOutcome_value (v : α) :
    MvResult.ofOutcome (Outcome.value v) = .value v := rfl

end Results

/-! ## Monomial orders -/

section Orders

variable {n : ℕ} (o : OrderKind n)

/-- No exponent vector is below itself. -/
public theorem orderLt_irrefl (a : Exponents n) : ¬o.Lt a a :=
  (monomialOrdersAreStrictTotalOrders n o).1 a

/-- The strict order of a monomial order is transitive. -/
public theorem orderLt_trans {a b c : Exponents n} (h₁ : o.Lt a b) (h₂ : o.Lt b c) : o.Lt a c :=
  (monomialOrdersAreStrictTotalOrders n o).2.1 a b c h₁ h₂

/-- A vector below another is not equal to it. -/
public theorem orderLt_ne {a b : Exponents n} (h : o.Lt a b) : a ≠ b :=
  fun e => orderLt_irrefl o b (e ▸ h)

/-- The comparison is `lt` exactly when the first vector is below the second. -/
public theorem compare_eq_lt_iff (a b : Exponents n) : o.compare a b = .lt ↔ o.Lt a b :=
  ((monomialOrdersAreStrictTotalOrders n o).2.2.2 a b).1

/-- The comparison is `eq` exactly for equal vectors. -/
public theorem compare_eq_eq_iff (a b : Exponents n) : o.compare a b = .eq ↔ a = b :=
  ((monomialOrdersAreStrictTotalOrders n o).2.2.2 a b).2.1

/-- The comparison is `gt` exactly when the first vector is above the second. -/
public theorem compare_eq_gt_iff (a b : Exponents n) : o.compare a b = .gt ↔ o.Lt b a :=
  ((monomialOrdersAreStrictTotalOrders n o).2.2.2 a b).2.2

end Orders

/-! ## Exponent vectors as vectors of Mathlib -/

section Vectors

variable {n : ℕ}

/-- The vector of Mathlib of an exponent vector has its exponents. -/
@[simp] public theorem toFinsupp_apply (e : Exponents n) (i : Fin n) : e.toFinsupp i = e i := rfl

/-- Exponent vectors that denote the same vector of Mathlib are equal. -/
public theorem toFinsupp_injective :
    Function.Injective (Exponents.toFinsupp : Exponents n → Fin n →₀ ℕ) :=
  Finsupp.equivFunOnFinite.symm.injective

/-- Every vector of Mathlib is the vector of its exponents. -/
@[simp] public theorem toFinsupp_coe (s : Fin n →₀ ℕ) : Exponents.toFinsupp (⇑s) = s :=
  Finsupp.equivFunOnFinite_symm_coe s

/-- The sum of the exponents of the vector of Mathlib is the total degree. -/
public theorem sum_toFinsupp (e : Exponents n) : (e.toFinsupp.sum fun _ k => k) = e.degree := by
  rw [Finsupp.sum_fintype _ _ fun _ => rfl]
  rfl

end Vectors

variable {P E : Type} {K : P → Type} [∀ p, CommRing (K p)] (M : Model P E K) (p : P) {n : ℕ}

/-! ## Interpretations of lists of terms -/

/-- The interpretation of the empty list is zero. -/
@[simp] public theorem interpret_nil : (⟨[]⟩ : MvPoly n E).interpret M p = 0 := by
  simp [MvPoly.interpret]

/-- The interpretation of the zero polynomial is zero. -/
@[simp] public theorem interpret_zero : (MvPoly.zero : MvPoly n E).interpret M p = 0 :=
  interpret_nil M p

/-- The interpretation of a list with a first term. -/
public theorem interpret_cons (t : Exponents n × E) (l : List (Exponents n × E)) :
    (⟨t :: l⟩ : MvPoly n E).interpret M p =
      monomial t.1.toFinsupp ((M p).interpret t.2) + (⟨l⟩ : MvPoly n E).interpret M p := by
  simp [MvPoly.interpret]

/-- The interpretation of two lists one after the other. -/
public theorem interpret_append (l₁ l₂ : List (Exponents n × E)) :
    (⟨l₁ ++ l₂⟩ : MvPoly n E).interpret M p =
      (⟨l₁⟩ : MvPoly n E).interpret M p + (⟨l₂⟩ : MvPoly n E).interpret M p := by
  simp [MvPoly.interpret]

/-- Lists of terms that are permutations of one another have one
interpretation. -/
public theorem interpret_perm {l₁ l₂ : List (Exponents n × E)} (h : l₁.Perm l₂) :
    (⟨l₁⟩ : MvPoly n E).interpret M p = (⟨l₂⟩ : MvPoly n E).interpret M p :=
  (h.map _).sum_eq

/-! ## Canonical lists -/

/-- The canonical form read through the terms: the monomials increase, and
each coefficient is canonical and does not denote zero. -/
public theorem canonical_iff_terms (o : OrderKind n) (a : MvPoly n E) :
    a.Canonical M p o ↔ a.terms.Pairwise (fun x y => o.Lt x.1 y.1) ∧
      ∀ x ∈ a.terms, (M p).canonical x.2 ∧ (M p).interpret x.2 ≠ 0 := by
  simp only [MvPoly.Canonical, MvPoly.monomials, MvPoly.coefficients, List.pairwise_map,
    List.forall_mem_map]

/-- The zero polynomial is canonical. -/
public theorem canonical_zero (o : OrderKind n) : (MvPoly.zero : MvPoly n E).Canonical M p o := by
  simp [canonical_iff_terms, MvPoly.zero]

/-- A list with a first term is canonical when the term lies below the rest,
its coefficient is canonical and not zero, and the rest is canonical. -/
public theorem canonical_cons_iff (o : OrderKind n) (t : Exponents n × E)
    (l : List (Exponents n × E)) :
    (⟨t :: l⟩ : MvPoly n E).Canonical M p o ↔
      (∀ x ∈ l, o.Lt t.1 x.1) ∧ ((M p).canonical t.2 ∧ (M p).interpret t.2 ≠ 0) ∧
        (⟨l⟩ : MvPoly n E).Canonical M p o := by
  simp only [canonical_iff_terms, List.pairwise_cons, List.forall_mem_cons]
  tauto

/-! ## Coefficients and support -/

/-- A monomial that no term has is a zero coefficient of the interpretation. -/
public theorem coeff_interpret_of_forall_ne (l : List (Exponents n × E)) (e : Exponents n)
    (h : ∀ x ∈ l, x.1 ≠ e) :
    ((⟨l⟩ : MvPoly n E).interpret M p).coeff e.toFinsupp = 0 := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp [interpret_cons, coeff_monomial, toFinsupp_injective.ne (h t List.mem_cons_self),
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- The coefficient of the interpretation of a canonical polynomial at a
stored monomial is the interpretation of the stored coefficient. -/
public theorem coeff_interpret_of_mem {o : OrderKind n} {a : MvPoly n E}
    (ha : a.Canonical M p o) {e : Exponents n} {c : E} (h : (e, c) ∈ a.terms) :
    (a.interpret M p).coeff e.toFinsupp = (M p).interpret c := by
  obtain ⟨l⟩ := a
  induction l with
  | nil => simp at h
  | cons t l ih =>
    obtain ⟨hlt, -, hl⟩ := (canonical_cons_iff M p o t l).1 ha
    rcases List.mem_cons.1 h with rfl | h
    · simp [interpret_cons, coeff_monomial,
        coeff_interpret_of_forall_ne M p l e fun x hx => (orderLt_ne o (hlt x hx)).symm]
    · simp [interpret_cons, coeff_monomial, ih hl h,
        toFinsupp_injective.ne (orderLt_ne o (hlt _ h))]

/-- The support of the interpretation of a canonical polynomial is the set of
the vectors of Mathlib of its monomials. -/
public theorem mem_support_interpret_iff {o : OrderKind n} {a : MvPoly n E}
    (ha : a.Canonical M p o) (s : Fin n →₀ ℕ) :
    s ∈ (a.interpret M p).support ↔ ∃ x ∈ a.terms, x.1.toFinsupp = s := by
  rw [mem_support_iff]
  constructor
  · intro h
    by_contra hne
    refine h ?_
    rw [← toFinsupp_coe s]
    exact coeff_interpret_of_forall_ne M p a.terms _ fun x hx e =>
      hne ⟨x, hx, by rw [e, toFinsupp_coe]⟩
  · rintro ⟨⟨e, c⟩, hx, rfl⟩
    rw [coeff_interpret_of_mem M p ha hx]
    exact (((canonical_iff_terms M p o a).1 ha).2 _ hx).2

/-- A canonical polynomial denotes zero exactly when it has no term. -/
public theorem interpret_eq_zero_iff {o : OrderKind n} {a : MvPoly n E}
    (ha : a.Canonical M p o) : a.interpret M p = 0 ↔ a.terms = [] := by
  refine ⟨fun h0 => ?_, fun h => ?_⟩
  · rcases hl : a.terms with _ | ⟨t, l⟩
    · rfl
    · have hmem : (t.1, t.2) ∈ a.terms := by rw [hl]; exact List.mem_cons_self
      have := coeff_interpret_of_mem M p ha hmem
      rw [h0] at this
      exact ((((canonical_iff_terms M p o a).1 ha).2 _ hmem).2 (by simpa using this.symm)).elim
  · obtain ⟨l⟩ := a
    simp only at h
    subst h
    exact interpret_nil M p

/-! ## Uniqueness -/

/-- A term of a canonical polynomial is a term of each other with its interpretation. -/
private theorem mem_of_interpret_eq (hu : (M p).Unique) {o : OrderKind n} {a b : MvPoly n E}
    (ha : a.Canonical M p o) (hb : b.Canonical M p o) (h : a.interpret M p = b.interpret M p)
    {x : Exponents n × E} (hx : x ∈ a.terms) : x ∈ b.terms := by
  obtain ⟨e, c⟩ := x
  have hca := ((canonical_iff_terms M p o a).1 ha).2 _ hx
  have hcoeff := coeff_interpret_of_mem M p ha hx
  rw [h] at hcoeff
  obtain ⟨⟨e', c'⟩, hy, he⟩ := (mem_support_interpret_iff M p hb e.toFinsupp).1
    (by rw [mem_support_iff, hcoeff]; exact hca.2)
  obtain rfl := toFinsupp_injective he
  rw [coeff_interpret_of_mem M p hb hy] at hcoeff
  rwa [hu c' c (((canonical_iff_terms M p o b).1 hb).2 _ hy).1 hca.1 hcoeff] at hy

/-- Canonical forms are unique: two canonical polynomials over one parent with
the same interpretation are equal, when the canonical elements of the parent
are unique. -/
public theorem eq_of_interpret_eq (hu : (M p).Unique) {o : OrderKind n} {a b : MvPoly n E}
    (ha : a.Canonical M p o) (hb : b.Canonical M p o) (h : a.interpret M p = b.interpret M p) :
    a = b := by
  have nodup : ∀ {c : MvPoly n E}, c.Canonical M p o → c.terms.Nodup := fun hc =>
    ((canonical_iff_terms M p o _).1 hc).1.imp fun hlt e => orderLt_ne o hlt (congrArg Prod.fst e)
  have perm := (List.perm_ext_iff_of_nodup (nodup ha) (nodup hb)).2 fun x =>
    ⟨mem_of_interpret_eq M p hu ha hb h, mem_of_interpret_eq M p hu hb ha h.symm⟩
  obtain ⟨la⟩ := a
  obtain ⟨lb⟩ := b
  congr 1
  exact perm.eq_of_pairwise (le := fun x y => o.Lt x.1 y.1)
    (fun _ _ _ _ h₁ h₂ => absurd (orderLt_trans o h₁ h₂) (orderLt_irrefl o _))
    ((canonical_iff_terms M p o _).1 ha).1 ((canonical_iff_terms M p o _).1 hb).1

variable {M} {R : CoefficientRing P E Empty}

/-- Two results that are canonical polynomials of a ring with one
interpretation are equal, when the canonical elements of its parent are
unique. -/
public theorem eq_of_yields {r : MultivariateRing P n} (hu : (M r.coefficients).Unique)
    {o o' : MvResult (MvPoly n E)} {x : MvPolynomial (Fin n) (K r.coefficients)}
    (h : r.Yields M o x) (h' : r.Yields M o' x) : o = o' := by
  obtain ⟨a, rfl, ha, hax⟩ := h
  obtain ⟨b, rfl, hb, hbx⟩ := h'
  rw [eq_of_interpret_eq M r.coefficients hu ha hb (hax.trans hbx.symm)]

/-! ## The canonical form of the polynomials of a ring -/

/-- Canonical forms are unique: two canonical polynomials of the ring `r`
that denote the same polynomial of Mathlib are equal. -/
public theorem unique (hR : ExactRing R M) (r : MultivariateRing P n) :
    (MultivariateRing.model M r).Unique :=
  fun _ _ ha hb h => eq_of_interpret_eq M r.coefficients (hR.1.unique _) ha hb h

/-- A polynomial of the ring `r` is canonical exactly when its monomials
increase under the order of `r` and each coefficient is canonical and
nonzero by the zero test. -/
public theorem canonical_iff (hR : ExactRing R M) (r : MultivariateRing P n) :
    ∀ a, (MultivariateRing.model M r).canonical a ↔ a.monomials.Pairwise r.order.Lt ∧
      ∀ c ∈ a.coefficients, (M r.coefficients).canonical c ∧
        R.zeroTest r.coefficients c = .value .nonzero := fun _ =>
  and_congr Iff.rfl <| forall₂_congr fun c _ =>
    ⟨fun h => ⟨h.1, (hR.2.nonzero _ c h.1).2 h.2⟩,
      fun h => ⟨h.1, (hR.2.nonzero _ c h.1).1 h.2⟩⟩

/-- The zero polynomial is a canonical polynomial of every ring that denotes
zero. -/
public theorem yields_zero (r : MultivariateRing P n) :
    r.Yields M (.value MvPoly.zero) 0 :=
  ⟨_, rfl, canonical_zero M r.coefficients r.order, interpret_zero M r.coefficients⟩

/-! ## Zero tests and monomials -/

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

/-- The polynomial of at most one term with a canonical coefficient, the zero polynomial when
the coefficient is zero, is a canonical polynomial that denotes the monomial of Mathlib. -/
public theorem monomial_yields (hR : ExactRing R M) (r : MultivariateRing P n) (e : Exponents n)
    {c : E} (hc : (M r.coefficients).canonical c) :
    r.Yields M (MvPoly.monomial R r.coefficients e c)
      (monomial e.toFinsupp ((M r.coefficients).interpret c)) := by
  by_cases h0 : (M r.coefficients).interpret c = 0
  · refine ⟨MvPoly.zero, ?_, canonical_zero M _ _, by simp [MultivariateRing.model, h0]⟩
    simp [MvPoly.monomial, testZero_of_eq_zero _ hR.2 hc h0]
  · refine ⟨⟨[(e, c)]⟩, ?_, ?_, by simp [MultivariateRing.model, interpret_cons]⟩
    · simp [MvPoly.monomial, testZero_of_ne_zero _ hR.2 hc h0]
    · exact (canonical_cons_iff M _ _ _ _).2 ⟨by simp, ⟨hc, h0⟩, canonical_zero M _ _⟩

/-! ## Normalization -/

/-- Insertion keeps the terms increasing and canonical and adds the term. -/
private theorem insertTerm_spec (hR : RingLaws R M) (o : OrderKind n) {t : Exponents n × E}
    (ht : (M p).canonical t.2) (acc : List (Exponents n × E))
    (hs : acc.Pairwise fun x y => o.Lt x.1 y.1) (hc : ∀ x ∈ acc, (M p).canonical x.2) :
    ∃ l, MvPoly.insertTerm R p o t acc = .value l ∧ l.Pairwise (fun x y => o.Lt x.1 y.1) ∧
      (∀ x ∈ l, (M p).canonical x.2) ∧
      (∀ e, o.Lt e t.1 → (∀ x ∈ acc, o.Lt e x.1) → ∀ x ∈ l, o.Lt e x.1) ∧
      (⟨l⟩ : MvPoly n E).interpret M p =
        (⟨acc⟩ : MvPoly n E).interpret M p + monomial t.1.toFinsupp ((M p).interpret t.2) := by
  induction acc with
  | nil =>
    refine ⟨[t], rfl, List.pairwise_singleton _ _, by simpa using ht, ?_, ?_⟩
    · simp only [List.mem_singleton]
      rintro e he - x rfl
      exact he
    · simp [interpret_cons]
  | cons u us ih =>
    rw [List.pairwise_cons] at hs
    have hu := hc u List.mem_cons_self
    have hus : ∀ x ∈ us, (M p).canonical x.2 := fun x hx => hc x (List.mem_cons_of_mem _ hx)
    cases h : o.compare t.1 u.1 with
    | lt =>
      have hlt := (compare_eq_lt_iff o _ _).1 h
      refine ⟨t :: u :: us, by simp [MvPoly.insertTerm, h], ?_, ?_, ?_, ?_⟩
      · refine List.pairwise_cons.2 ⟨fun x hx => ?_, List.pairwise_cons.2 hs⟩
        rcases List.mem_cons.1 hx with rfl | hx
        exacts [hlt, orderLt_trans o hlt (hs.1 x hx)]
      · simpa [ht] using hc
      · intro e he hall x hx
        rcases List.mem_cons.1 hx with rfl | hx
        exacts [he, hall x hx]
      · simp only [interpret_cons]
        abel
    | eq =>
      have heq := (compare_eq_eq_iff o _ _).1 h
      obtain ⟨s, hsv, hsc, hsi⟩ := hR.add p u.2 t.2 hu ht
      refine ⟨(u.1, s) :: us, by simp [MvPoly.insertTerm, h, hsv], List.pairwise_cons.2 hs, ?_,
        ?_, ?_⟩
      · simpa [hsc] using hus
      · intro e _ hall x hx
        rcases List.mem_cons.1 hx with rfl | hx
        exacts [hall u List.mem_cons_self, hall x (List.mem_cons_of_mem _ hx)]
      · simp only [interpret_cons, hsi, heq, map_add]
        abel
    | gt =>
      have hgt := (compare_eq_gt_iff o _ _).1 h
      obtain ⟨l, hl, hls, hlc, hlb, hli⟩ := ih hs.2 hus
      refine ⟨u :: l, by simp [MvPoly.insertTerm, h, hl], ?_, ?_, ?_, ?_⟩
      · exact List.pairwise_cons.2 ⟨hlb u.1 hgt hs.1, hls⟩
      · simpa [hu] using hlc
      · intro e he hall x hx
        rcases List.mem_cons.1 hx with rfl | hx
        exacts [hall _ List.mem_cons_self,
          hlb e he (fun y hy => hall y (List.mem_cons_of_mem _ hy)) x hx]
      · simp only [interpret_cons, hli]
        abel

/-- Insertion of each term keeps the terms increasing and canonical and adds them. -/
private theorem insertAll_spec (hR : RingLaws R M) (o : OrderKind n)
    (ts : List (Exponents n × E)) (hts : ∀ t ∈ ts, (M p).canonical t.2)
    (acc : List (Exponents n × E)) (hs : acc.Pairwise fun x y => o.Lt x.1 y.1)
    (hc : ∀ x ∈ acc, (M p).canonical x.2) :
    ∃ l, MvPoly.insertAll R p o acc ts = .value l ∧ l.Pairwise (fun x y => o.Lt x.1 y.1) ∧
      (∀ x ∈ l, (M p).canonical x.2) ∧
      (⟨l⟩ : MvPoly n E).interpret M p =
        (⟨acc⟩ : MvPoly n E).interpret M p + (⟨ts⟩ : MvPoly n E).interpret M p := by
  induction ts generalizing acc with
  | nil => exact ⟨acc, rfl, hs, hc, by simp⟩
  | cons t ts ih =>
    obtain ⟨l₁, h₁, hs₁, hc₁, -, hi₁⟩ :=
      insertTerm_spec p hR o (hts t List.mem_cons_self) acc hs hc
    obtain ⟨l, hl, hls, hlc, hli⟩ :=
      ih (fun x hx => hts x (List.mem_cons_of_mem _ hx)) l₁ hs₁ hc₁
    refine ⟨l, by simp [MvPoly.insertAll, h₁, hl], hls, hlc, ?_⟩
    rw [hli, hi₁, interpret_cons]
    abel

/-- Dropping the zero terms keeps a sublist with nonzero coefficients and its meaning. -/
private theorem dropZeros_spec (hz : ZeroTestExact R M) (l : List (Exponents n × E))
    (hc : ∀ x ∈ l, (M p).canonical x.2) :
    ∃ l', MvPoly.dropZeros R p l = .value l' ∧ l'.Sublist l ∧
      (∀ x ∈ l', (M p).interpret x.2 ≠ 0) ∧
      (⟨l'⟩ : MvPoly n E).interpret M p = (⟨l⟩ : MvPoly n E).interpret M p := by
  induction l with
  | nil => exact ⟨[], rfl, List.Sublist.slnil, by simp, rfl⟩
  | cons t l ih =>
    obtain ⟨l', hl', hsub, hnz, hli⟩ := ih fun x hx => hc x (List.mem_cons_of_mem _ hx)
    have ht := hc t List.mem_cons_self
    by_cases h0 : (M p).interpret t.2 = 0
    · refine ⟨l', by simp [MvPoly.dropZeros, testZero_of_eq_zero p hz ht h0, hl'],
        hsub.cons t, hnz, ?_⟩
      rw [hli, interpret_cons, h0, map_zero, zero_add]
    · refine ⟨t :: l', by simp [MvPoly.dropZeros, testZero_of_ne_zero p hz ht h0, hl'],
        hsub.cons_cons t, ?_, ?_⟩
      · simpa [h0] using hnz
      · simp only [interpret_cons, hli]

/-- Normalization of terms with canonical coefficients in the ring `r` yields
the canonical form of their sum. -/
public theorem normalize_yields (hR : ExactRing R M) (r : MultivariateRing P n)
    {ts : List (Exponents n × E)} (hts : ∀ t ∈ ts, (M r.coefficients).canonical t.2) :
    r.Yields M (r.normalize R ts) ((⟨ts⟩ : MvPoly n E).interpret M r.coefficients) := by
  obtain ⟨l, hl, hls, hlc, hli⟩ :=
    insertAll_spec r.coefficients hR.1 r.order ts hts [] List.Pairwise.nil (by simp)
  obtain ⟨l', hl', hsub, hnz, hi'⟩ := dropZeros_spec r.coefficients hR.2 l hlc
  refine ⟨⟨l'⟩, by simp [MultivariateRing.normalize, MvPoly.normalize, hl, hl'], ?_, ?_⟩
  · exact (canonical_iff_terms M _ _ _).2
      ⟨hls.sublist hsub, fun x hx => ⟨hlc x (hsub.subset hx), hnz x hx⟩⟩
  · change MvPoly.interpret M r.coefficients ⟨l'⟩ = _
    rw [hi', hli, interpret_nil, zero_add]

/-- A permutation of terms with canonical coefficients normalizes to the same
result in the ring `r`. -/
public theorem normalize_perm (hR : ExactRing R M) (r : MultivariateRing P n)
    {ts : List (Exponents n × E)} (hts : ∀ t ∈ ts, (M r.coefficients).canonical t.2)
    {us : List (Exponents n × E)} (h : us.Perm ts) : r.normalize R us = r.normalize R ts := by
  have hus := normalize_yields hR r fun t ht => hts t (h.subset ht)
  rw [interpret_perm M _ h] at hus
  exact eq_of_yields (hR.1.unique _) hus (normalize_yields hR r hts)

/-- When every element of the coefficient ring has a canonical form, so does
every polynomial of Mathlib in the ring `r`: the normalization of its terms. -/
public theorem complete (hR : ExactRing R M) (r : MultivariateRing P n) :
    (M r.coefficients).Complete → (MultivariateRing.model M r).Complete := by
  intro hc X
  have hc' : ∀ x, ∃ e, (M r.coefficients).canonical e ∧ (M r.coefficients).interpret e = x :=
    hc
  choose f hf using hc'
  obtain ⟨a, -, hac, hai⟩ := normalize_yields (R := R) hR r
    (ts := X.support.toList.map fun (s : Fin n →₀ ℕ) => ((⇑s : Exponents n), f (X.coeff s)))
    (by simp [hf])
  refine ⟨a, hac, hai.trans ?_⟩
  simp [MvPoly.interpret, Function.comp_def, hf, support_sum_monomial_coeff]

end Kalyx.Proofs.Multivariate.Canonical
