module

public import Kalyx.Proofs.Polynomials.Conversion
import Kalyx.Proofs.Terms.Order

/-!
# Expanding the conversion of a polynomial back

An unregistered helper module of the proofs about the univariate polynomials;
it proves no registered statement. It shows that the conversion of a
canonical polynomial `a` of `ℚ[x]` back to a term expands into `a` again,
under limits that admit `a` and the depth of the term (`toTerm_expand`):

* the conversion is computed: the term of a term `c xᵈ` is the number `c`,
  the power `x^d` (the symbol for `d = 1`) for `c = 1`, and otherwise the
  product of `c` and that power; the cores increase in the order of terms as
  their degrees do, so the sum keeps them in the stored order, and is the
  number of the constant, the term of a single term, or a sum node;
* the expansion of that term forms, in turn, the constants of the
  coefficients, the powers `xʲ` of repeated squaring with `j` at most a
  degree of `a`, the terms of `a`, and the sums of the first terms of `a`;
* the storage cost of each of these polynomials is at most that of `a`, and
  its degree at most that of `a`, so each passes the checks that `a` passes,
  and the last sum is `a`.
-/

namespace Kalyx.Proofs.Polynomials.Roundtrip

open Kalyx.Spec.Fields Kalyx.Spec.Polynomials Kalyx.Statements.Polynomials Polynomial
open Kalyx.Spec.Terms (Term Orders mkSymbol mkSum mkProduct mkPower exponentBound checkExponent
  sumParts mergeMonomials cancelMonomials assembleSum maxBases uncovered sortedTerms sortBy
  insertBy mergeAdjacent)
open Kalyx.Proofs.Polynomials.Canonical Kalyx.Proofs.Polynomials.Operations
open Kalyx.Proofs.Polynomials.Expansion Kalyx.Proofs.Polynomials.Conversion

/-! ## The constructors on the terms of a polynomial -/

section Constructors

open Kalyx.Spec.Terms

private theorem maxBases_nil (o : Orders) : maxBases o [] = [] := by
  simp [maxBases, sortedTerms, sortBy, mergeAdjacent]

private theorem mkProduct_symbol (o : Orders) {me : ℕ} {q : ℚ} (s : String) (hq : q ≠ 0)
    (hme : 1 ≤ exponentBound me) :
    mkProduct o me [.number q, .symbol s] =
      .value (if q = 1 then .symbol s else .product q [.symbol s]) := by
  have h1 : ¬ exponentBound me < 1 := by omega
  simp [mkProduct, productParts, factorParts, itemParts, buildProduct, settleItems, mergeItems,
    sortBy, insertBy, mergeAdjacent, reduceItem, checkExponent, h1, rootOf, Term.isCondition,
    ProductParts.append, ProductParts.unit, itemFactor, uncovered, Term.negBasesList,
    maxBases_nil, assembleProduct, hq, Term.imaginaryUnit, Term.depthList, Term.depth]

private theorem mkPower_symbol (o : Orders) {me k : ℕ} (s : String) (hk : 2 ≤ k)
    (hme : k ≤ exponentBound me) :
    mkPower o me (.symbol s) k = .value (.power (.symbol s) k) := by
  have h1 : ¬ exponentBound me < k := by omega
  have h2 : (k : ℤ) ≠ 1 := by omega
  have h3 : k ≠ 0 := by omega
  simp [mkPower, checkExponent, h1, h2, h3, Term.isCondition, distributedPower, mergedPower,
    mergePowers, buildProduct, settleItems, mergeItems, sortBy, insertBy, mergeAdjacent,
    reduceItem, rootOf, ProductParts.append, ProductParts.unit, itemFactor, uncovered,
    Term.negBasesList, Term.negBases, maxBases_nil, assembleProduct, Term.imaginaryUnit,
    Term.depthList, Term.depth]

private theorem mkProduct_power (o : Orders) {me k : ℕ} {q : ℚ} (s : String) (hq : q ≠ 0)
    (hk : 2 ≤ k) (hme : k ≤ exponentBound me) :
    mkProduct o me [.number q, .power (.symbol s) k] =
      .value (if q = 1 then .power (.symbol s) k else .product q [.power (.symbol s) k]) := by
  have h1 : ¬ exponentBound me < k := by omega
  have h2 : (k : ℤ) ≠ 1 := by omega
  have h3 : k ≠ 0 := by omega
  simp [mkProduct, productParts, factorParts, itemParts, buildProduct, settleItems, mergeItems,
    sortBy, insertBy, mergeAdjacent, reduceItem, checkExponent, h1, h2, h3, rootOf,
    Term.isCondition, ProductParts.append, ProductParts.unit, itemFactor, uncovered,
    Term.negBasesList, Term.negBases, maxBases_nil, assembleProduct, hq, Term.imaginaryUnit,
    Term.depthList, Term.depth]

end Constructors

/-! ## The term of a polynomial -/

/-- The term of the variable `s` to the power `d ≥ 1`. -/
private def core (s : String) (d : ℕ) : Term := if d = 1 then .symbol s else .power (.symbol s) d

/-- The term of the term `c xᵈ` of a polynomial. -/
private def mono (s : String) (y : ℕ × Fraction) : Term :=
  if y.1 = 0 then .number y.2.interpret
  else if y.2.interpret = 1 then core s y.1 else .product y.2.interpret [core s y.1]

/-- The monomials of the sum of the terms of the terms of positive degree. -/
private def monos (s : String) (l : List (ℕ × Fraction)) : List (ℚ × Term) :=
  l.map fun y => (y.2.interpret, core s y.1)

private theorem monomialTerm_eq (o : Orders) {me : ℕ} (s : String) {d : ℕ} {f : Fraction}
    (hf : f.interpret ≠ 0) (hd : d ≤ exponentBound me) :
    monomialTerm o me (.symbol s) (d, f) = .value (mono s (d, f)) := by
  rcases d with _ | _ | d
  · simp [monomialTerm, mono]
  · simp only [monomialTerm, mkProduct_symbol o s hf hd, mono, core]
    split <;> simp
  · simp only [monomialTerm, mkPower_symbol o s (k := d + 2) (by omega) hd,
      Kalyx.Proofs.Terms.bind_value, mono, core]
    rw [mkProduct_power o s hf (by omega) hd]
    simp

private theorem mapM_eq (o : Orders) {me : ℕ} (s : String) :
    ∀ l : List (ℕ × Fraction), (∀ y ∈ l, y.2.interpret ≠ 0 ∧ y.1 ≤ exponentBound me) →
      l.mapM (monomialTerm o me (.symbol s)) = .value (l.map (mono s)) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons y l ih =>
    intro h
    obtain ⟨d, f⟩ := y
    obtain ⟨hf, hd⟩ := h (d, f) List.mem_cons_self
    rw [List.mapM_cons, monomialTerm_eq o s hf hd, Kalyx.Proofs.Terms.bind_value,
      ih fun y hy => h y (List.mem_cons_of_mem _ hy), Kalyx.Proofs.Terms.bind_value]
    rfl

private theorem sumParts_core (s : String) (d : ℕ) (ts : List Term) :
    sumParts (core s d :: ts) = ((sumParts ts).1, (1, core s d) :: (sumParts ts).2) := by
  unfold core
  split <;> simp [sumParts]

private theorem sumParts_monos (s : String) :
    ∀ l : List (ℕ × Fraction), (∀ y ∈ l, y.1 ≠ 0) → sumParts (l.map (mono s)) = (0, monos s l) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons y l ih =>
    intro h
    obtain ⟨d, f⟩ := y
    have hd := h (d, f) List.mem_cons_self
    have ih' := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [List.map_cons, mono, hd, ↓reduceIte, monos]
    unfold monos at ih'
    split
    · rename_i h1
      simp [sumParts_core, ih', h1]
    · simp [sumParts, ih', Kalyx.Spec.Terms.productCore]

private theorem mono_not_condition (s : String) (y : ℕ × Fraction) :
    (mono s y).isCondition = false := by
  unfold mono core
  split
  · rfl
  · split <;> split <;> rfl

private theorem core_lt {o : Orders} (ho : o.Total) (s : String) {d e : ℕ} (hd : 1 ≤ d)
    (he : d < e) : Term.cmp o (core s d) (core s e) = .lt := by
  have he1 : e ≠ 1 := by omega
  unfold core
  simp only [he1, ↓reduceIte]
  split
  · exact (Kalyx.Proofs.Terms.termOrderIsTotal o ho).2.2 _ _ (by simp [Term.rank])
  · have hs : Kalyx.Spec.Terms.nameCmp s s = .eq := by
      have := Kalyx.Proofs.Terms.nameCmp_total.2
      exact Std.ReflCmp.compare_self
    have hde : compare (d : ℤ) (e : ℤ) = .lt := compare_lt_iff_lt.2 (by omega)
    simp [Term.cmp, Term.firstDifference, hs, hde, Kalyx.Spec.Terms.Difference.ofOrdering,
      Kalyx.Spec.Terms.Difference.andThen, Kalyx.Spec.Terms.Difference.order]

/-- The sum of the terms of positive degree keeps them in the stored order. -/
private theorem mkSum_monos {o : Orders} (ho : o.Total) (s : String) (c : ℚ)
    (l : List (ℕ × Fraction)) (hl : l.Pairwise fun x y => x.1 < y.1) (hpos : ∀ y ∈ l, y.1 ≠ 0)
    (hc : ∀ y ∈ l, y.2.interpret ≠ 0) (ts : List Term)
    (hts : ts.any Term.isCondition = false) (hparts : sumParts ts = (c, monos s l)) :
    mkSum o ts = .value (assembleSum c (monos s l)) := by
  have htot := (Kalyx.Proofs.Terms.termOrderIsTotal o ho).1
  have := htot.1
  have hm : mergeMonomials o (monos s l) = monos s l := by
    refine Kalyx.Proofs.Terms.mergeMonomials_eq_self htot ?_
    rw [Kalyx.Proofs.Terms.strictlyIncreasing_iff_pairwise]
    unfold monos
    rw [List.map_map, List.pairwise_map]
    refine hl.imp_of_mem fun {x y} hx _ hxy => core_lt ho s ?_ hxy
    have := hpos x hx
    omega
  have hcz : ∀ m ∈ monos s l, m.1 ≠ 0 := by
    intro m hm
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hm
    exact_mod_cast hc y hy
  have h1 : (monos s l).filter (fun m => !decide (m.1 = 0)) = monos s l :=
    List.filter_eq_self.2 fun m hm => by simpa using hcz m hm
  have h2 : (monos s l).filter (fun m => decide (m.1 = 0)) = [] :=
    List.filter_eq_nil_iff.2 fun m hm => by simpa using hcz m hm
  simp [mkSum, hts, hparts, hm, cancelMonomials, h1, h2, Term.negBasesPairs, uncovered,
    maxBases_nil]

/-! ## Storage costs over the rationals -/

section Storage

variable (r : PolynomialRing Rationals)

/-- The storage cost of a term of a polynomial of `r`. -/
private abbrev cost (y : ℕ × Fraction) : Storage :=
  termCost (rationalRing.measure r.coefficients y.2) r.variableName.utf8ByteSize y.1

private theorem storage_cons (y : ℕ × Fraction) (ys : List (ℕ × Fraction)) :
    r.storage rationalRing ⟨y :: ys⟩ =
      ⟨((y :: ys).map fun x => (cost r x).nodes).sum + ys.length,
        ((y :: ys).map fun x => (cost r x).bytes).sum + 4 * ys.length +
          if (y :: ys).all (·.1 == 0) then r.variableName.utf8ByteSize else 0⟩ := by
  simp only [PolynomialRing.storage, List.map_map]
  rfl

private theorem measure_eq (f : Fraction) : rationalRing.measure r.coefficients f =
    ⟨1, f.num.natAbs.size + f.den.natAbs.size + 3⟩ := rfl

private theorem measure_nodes (f : Fraction) : (rationalRing.measure r.coefficients f).nodes = 1 :=
  rfl

private theorem measure_bytes_eq (f : Fraction) : (rationalRing.measure r.coefficients f).bytes =
    f.num.natAbs.size + f.den.natAbs.size + 3 := rfl

private theorem cost_nodes (y : ℕ × Fraction) : 1 ≤ (cost r y).nodes := by
  obtain ⟨_ | _ | d, f⟩ := y <;> (simp only [cost, termCost, measure_nodes]; omega)

private theorem measure_bytes {f : Fraction} (hf : f.Reduced) :
    4 ≤ (rationalRing.measure r.coefficients f).bytes := by
  have : 0 < f.den.natAbs.size := Nat.size_pos.2 (by have := hf.1; omega)
  rw [measure_bytes_eq]
  omega

private theorem measure_bytes_five {f : Fraction} (hf : f.Reduced) (hf0 : f.interpret ≠ 0) :
    5 ≤ (rationalRing.measure r.coefficients f).bytes := by
  have h1 : 0 < f.den.natAbs.size := Nat.size_pos.2 (by have := hf.1; omega)
  have h2 : 0 < f.num.natAbs.size := Nat.size_pos.2 (by
    rcases Nat.eq_zero_or_pos f.num.natAbs with h | h
    · exact absurd (by simp [Fraction.interpret, Int.natAbs_eq_zero.1 h]) hf0
    · exact h)
  rw [measure_bytes_eq]
  omega

private theorem cost_bytes {y : ℕ × Fraction} (hy : y.2.Reduced) : 4 ≤ (cost r y).bytes := by
  have := measure_bytes r hy
  obtain ⟨_ | _ | d, f⟩ := y <;> simp only [cost, termCost] at * <;> omega

private theorem cost_bytes_pos {y : ℕ × Fraction} (hy : y.1 ≠ 0) :
    r.variableName.utf8ByteSize ≤ (cost r y).bytes := by
  obtain ⟨_ | _ | d, f⟩ := y
  · exact absurd rfl hy
  all_goals (simp only [cost, termCost]; omega)

/-- A sublist of terms costs at most what the list costs. -/
private theorem storage_le_of_sublist {l l' : List (ℕ × Fraction)} (h : l.Sublist l')
    (hl' : ∀ y ∈ l', y.2.Reduced) :
    (r.storage rationalRing ⟨l⟩).nodes ≤ (r.storage rationalRing ⟨l'⟩).nodes ∧
      (r.storage rationalRing ⟨l⟩).bytes ≤ (r.storage rationalRing ⟨l'⟩).bytes := by
  obtain ⟨e, he⟩ := h.exists_perm_append
  have hsum : ∀ g : ℕ × Fraction → ℕ, (l'.map g).sum = (l.map g).sum + (e.map g).sum := by
    intro g
    rw [(he.map g).sum_eq, List.map_append, List.sum_append]
  have hlen := he.length_eq
  rw [List.length_append] at hlen
  rcases l with _ | ⟨y, ys⟩
  · rcases l' with _ | ⟨y', ys'⟩
    · exact ⟨le_rfl, le_rfl⟩
    · rw [storage_cons]
      have h1 := cost_nodes r y'
      have h2 := cost_bytes r (hl' y' List.mem_cons_self)
      simp only [PolynomialRing.storage, List.map_cons, List.sum_cons]
      constructor <;> omega
  · rcases l' with _ | ⟨y', ys'⟩
    · exact absurd h (by simp)
    · rw [storage_cons, storage_cons]
      have hn := hsum fun x => (cost r x).nodes
      have hb := hsum fun x => (cost r x).bytes
      simp only [List.length_cons] at hlen
      refine ⟨by simp only; omega, ?_⟩
      simp only
      split
      · rename_i hall
        split
        · omega
        · rename_i hall'
          obtain ⟨z, hz, hz0⟩ : ∃ z ∈ y' :: ys', z.1 ≠ 0 := by
            by_contra hne
            push Not at hne
            exact hall' (List.all_eq_true.2 fun z hz => by simpa using hne z hz)
          have hze : z ∈ e := by
            rcases List.mem_append.1 (he.mem_iff.1 hz) with hz' | hz'
            · exact absurd (by simpa using List.all_eq_true.1 hall z hz') hz0
            · exact hz'
          have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun x => (cost r x).bytes) hze)
          have := cost_bytes_pos r hz0
          omega
      · split <;> omega

/-- `xʲ` costs at most a term `c xᵈ` with `1 ≤ j ≤ d`. -/
private theorem storage_power_le {j d : ℕ} {f : Fraction} (hf : f.Reduced) (hf0 : f.interpret ≠ 0)
    (hj : 1 ≤ j) (hjd : j ≤ d) :
    (r.storage rationalRing ⟨[(j, Fraction.ofRat 1)]⟩).nodes ≤
        (r.storage rationalRing ⟨[(d, f)]⟩).nodes ∧
      (r.storage rationalRing ⟨[(j, Fraction.ofRat 1)]⟩).bytes ≤
        (r.storage rationalRing ⟨[(d, f)]⟩).bytes := by
  have h5 := measure_bytes_five r hf hf0
  have h1 : (rationalRing.measure r.coefficients (Fraction.ofRat 1)) = ⟨1, 5⟩ := by
    simp [rationalRing, Rationals.field, Fraction.ofRat]
  have hn : (rationalRing.measure r.coefficients f).nodes = 1 := rfl
  rw [storage_cons, storage_cons]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_nil,
    List.all_cons, List.all_nil, Bool.and_true, cost, h1]
  rcases j with _ | _ | j
  · omega
  · rcases d with _ | _ | d
    · omega
    · simp [termCost, hn]
      omega
    · simp [termCost, hn]
      omega
  · rcases d with _ | _ | d
    · omega
    · omega
    · have := Nat.size_le_size (show j + 2 ≤ d + 2 by omega)
      simp [termCost, hn]
      omega

/-- A constant costs at most a term `c xᵈ` of the same coefficient. -/
private theorem storage_const_le {d : ℕ} (f : Fraction) (hd : d ≠ 0) :
    (r.storage rationalRing ⟨[(0, f)]⟩).nodes ≤ (r.storage rationalRing ⟨[(d, f)]⟩).nodes ∧
      (r.storage rationalRing ⟨[(0, f)]⟩).bytes ≤ (r.storage rationalRing ⟨[(d, f)]⟩).bytes := by
  rw [storage_cons, storage_cons]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_nil,
    List.all_cons, List.all_nil, Bool.and_true, cost]
  rcases d with _ | _ | d
  · exact absurd rfl hd
  · simp [termCost]
  · simp [termCost]
    omega

end Storage

/-! ## Checks that pass -/

/-- A polynomial whose degree and storage cost are at most those of a
polynomial that passes the checks passes them too. -/
private theorem check_of_le {L : Limits} {r : PolynomialRing Rationals} {a b : Poly Fraction}
    (h : r.check rationalRing L a = .value a) (hd : b.degree.getD 0 ≤ a.degree.getD 0)
    (hn : (r.storage rationalRing b).nodes ≤ (r.storage rationalRing a).nodes)
    (hb : (r.storage rationalRing b).bytes ≤ (r.storage rationalRing a).bytes) :
    r.check rationalRing L b = .value b := by
  unfold PolynomialRing.check checkDegree checkStorage at *
  by_cases e1 : exponentBound L.maxExponent < a.degree.getD 0
  · simp [e1] at h
  by_cases e2 : L.maxNodes < (r.storage rationalRing a).nodes
  · simp [e1, e2] at h
  by_cases e3 : L.maxStorageBytes < (r.storage rationalRing a).bytes
  · simp [e1, e2, e3] at h
  have f1 : ¬ exponentBound L.maxExponent < b.degree.getD 0 := by omega
  have f2 : ¬ L.maxNodes < (r.storage rationalRing b).nodes := by omega
  have f3 : ¬ L.maxStorageBytes < (r.storage rationalRing b).bytes := by omega
  simp [f1, f2, f3]

/-- The degree of a polynomial that passes the checks is within the bound. -/
private theorem degree_le_of_check {L : Limits} {r : PolynomialRing Rationals} {a : Poly Fraction}
    (h : r.check rationalRing L a = .value a) : a.degree.getD 0 ≤ exponentBound L.maxExponent := by
  unfold PolynomialRing.check checkDegree at h
  by_contra e
  simp [not_le.1 e] at h

/-- The degree of the representation is at most a bound on its degrees. -/
private theorem degree_getD_le {l : List (ℕ × Fraction)} {D : ℕ} (h : ∀ y ∈ l, y.1 ≤ D) :
    (⟨l⟩ : Poly Fraction).degree.getD 0 ≤ D := by
  cases hl : l.getLast? with
  | none => simp [Poly.degree, hl]
  | some y => simpa [Poly.degree, hl] using h y (List.mem_of_getLast? hl)

/-- The degree of the representation of a single term. -/
private theorem degree_single (d : ℕ) (f : Fraction) : (⟨[(d, f)]⟩ : Poly Fraction).degree.getD 0 = d :=
  rfl

section Steps

variable {L : Limits} {r : PolynomialRing Rationals} {a : Poly Fraction}

/-- Every degree of a canonical polynomial is at most its degree. -/
private theorem le_degree (ha : a.Canonical Rationals.model r.coefficients) {y : ℕ × Fraction}
    (hy : y ∈ a.terms) : y.1 ≤ a.degree.getD 0 := by
  cases hl : a.terms.getLast? with
  | none => simp [List.getLast?_eq_none_iff.1 hl] at hy
  | some z =>
    have := le_of_getLast? Rationals.model r.coefficients ha (d := z.1) (c := z.2) (by simp [hl]) y hy
    simpa [Poly.degree, hl] using this

private theorem coeff_of_mem (ha : a.Canonical Rationals.model r.coefficients) {y : ℕ × Fraction}
    (hy : y ∈ a.terms) : y.2.Reduced ∧ y.2.interpret ≠ 0 :=
  ((canonical_iff Rationals.model r.coefficients a).1 ha).2 y hy

/-- A sublist of the terms of `a` passes the checks. -/
private theorem check_sublist (ha : a.Canonical Rationals.model r.coefficients)
    (hcheck : r.check rationalRing L a = .value a) {l : List (ℕ × Fraction)}
    (hl : l.Sublist a.terms) : r.check rationalRing L ⟨l⟩ = .value ⟨l⟩ := by
  obtain ⟨hn, hb⟩ := storage_le_of_sublist r hl fun y hy => (coeff_of_mem ha hy).1
  exact check_of_le hcheck (degree_getD_le fun y hy => le_degree ha (hl.subset hy)) hn hb

/-- The power `xʲ`, `1 ≤ j ≤ d` for a term `c xᵈ` of `a`, passes the checks. -/
private theorem check_power (ha : a.Canonical Rationals.model r.coefficients)
    (hcheck : r.check rationalRing L a = .value a) {d j : ℕ} {f : Fraction} (hy : (d, f) ∈ a.terms)
    (hj : 1 ≤ j) (hjd : j ≤ d) :
    r.check rationalRing L ⟨[(j, Fraction.ofRat 1)]⟩ = .value ⟨[(j, Fraction.ofRat 1)]⟩ := by
  obtain ⟨hf, hf0⟩ := coeff_of_mem ha hy
  obtain ⟨hn, hb⟩ := storage_power_le r hf hf0 hj hjd
  obtain ⟨hn', hb'⟩ := storage_le_of_sublist r (List.singleton_sublist.2 hy)
    fun y hy => (coeff_of_mem ha hy).1
  exact check_of_le hcheck (by rw [degree_single]; exact hjd.trans (le_degree ha hy))
    (hn.trans hn') (hb.trans hb')

/-- The constant of a coefficient of `a` passes the checks. -/
private theorem check_const (ha : a.Canonical Rationals.model r.coefficients)
    (hcheck : r.check rationalRing L a = .value a) {d : ℕ} {f : Fraction} (hy : (d, f) ∈ a.terms) :
    r.check rationalRing L ⟨[(0, f)]⟩ = .value ⟨[(0, f)]⟩ := by
  by_cases hd : d = 0
  · subst hd
    exact check_sublist ha hcheck (List.singleton_sublist.2 hy)
  · obtain ⟨hn, hb⟩ := storage_const_le r f hd
    obtain ⟨hn', hb'⟩ := storage_le_of_sublist r (List.singleton_sublist.2 hy)
      fun y hy => (coeff_of_mem ha hy).1
    exact check_of_le hcheck (by rw [degree_single]; exact Nat.zero_le _) (hn.trans hn')
      (hb.trans hb')

/-! ## The operations of the expansion -/

/-- A canonical polynomial that denotes a monomial is its single term. -/
private theorem eq_single {b : Poly Fraction} (hb : b.Canonical Rationals.model r.coefficients)
    {d : ℕ} {q : ℚ} (hq : q ≠ 0) (h : b.interpret Rationals.model r.coefficients = monomial d q) :
    b = ⟨[(d, Fraction.ofRat q)]⟩ := by
  refine eq_of_interpret_eq Rationals.model r.coefficients (rationalRing_exact.1.unique _) hb ?_ ?_
  · rw [canonical_cons_iff]
    exact ⟨by simp, ⟨ofRat_reduced q, by simpa [Rationals.model] using hq⟩,
      canonical_nil Rationals.model r.coefficients⟩
  · rw [h, interpret_cons, interpret_nil, add_zero]
    simp [Rationals.model]

private theorem ofRat_one : Fraction.ofRat 1 = rationalRing.one r.coefficients := by
  simp [Fraction.ofRat, rationalRing, Rationals.field]

/-- The constant of a nonzero coefficient. -/
private theorem constant_eq {f : Fraction} (hf : f.Reduced) (hf0 : f.interpret ≠ 0)
    (hc : r.check rationalRing L ⟨[(0, f)]⟩ = .value ⟨[(0, f)]⟩) :
    r.constant rationalRing L f = .value ⟨[(0, f)]⟩ := by
  unfold PolynomialRing.constant Poly.monomial
  rw [appendNonzero_of_ne_zero (M := Rationals.model) rationalRing_exact.2 _ 0 hf hf0,
    append_of_lt f (by simp [Poly.zero])]
  simpa [Poly.zero] using hc

/-- The constant of zero. -/
private theorem constant_zero (hc : r.check rationalRing L Poly.zero = .value Poly.zero) :
    r.constant rationalRing L (Fraction.ofRat 0) = .value Poly.zero := by
  unfold PolynomialRing.constant Poly.monomial
  rw [appendNonzero_of_eq_zero (M := Rationals.model) (p := r.coefficients) rationalRing_exact.2
    _ 0 (ofRat_reduced 0) (by simp [Rationals.model])]
  simpa using hc

/-- The product of two single terms that passes the checks. -/
private theorem multiply_single {d₁ d₂ : ℕ} {f₁ f₂ : Fraction} (hf₁ : f₁.Reduced)
    (hf₁0 : f₁.interpret ≠ 0) (hf₂ : f₂.Reduced) (hf₂0 : f₂.interpret ≠ 0)
    (hc : r.check rationalRing L ⟨[(d₁ + d₂, Fraction.ofRat (f₁.interpret * f₂.interpret))]⟩ =
      .value ⟨[(d₁ + d₂, Fraction.ofRat (f₁.interpret * f₂.interpret))]⟩) :
    r.multiply rationalRing L ⟨[(d₁, f₁)]⟩ ⟨[(d₂, f₂)]⟩ =
      .value ⟨[(d₁ + d₂, Fraction.ofRat (f₁.interpret * f₂.interpret))]⟩ := by
  have hb₁ : (⟨[(d₁, f₁)]⟩ : Poly Fraction).Canonical Rationals.model r.coefficients :=
    (canonical_cons_iff _ _ _ _).2 ⟨by simp, ⟨hf₁, hf₁0⟩, canonical_nil _ _⟩
  have hb₂ : (⟨[(d₂, f₂)]⟩ : Poly Fraction).Canonical Rationals.model r.coefficients :=
    (canonical_cons_iff _ _ _ _).2 ⟨by simp, ⟨hf₂, hf₂0⟩, canonical_nil _ _⟩
  obtain ⟨w, hw, hwc, hwi⟩ := product_spec rationalRing_exact hb₁ hb₂
  have hw' := eq_single hwc (mul_ne_zero hf₁0 hf₂0) (d := d₁ + d₂) (by
    rw [hwi, interpret_cons, interpret_cons, interpret_nil, add_zero, add_zero,
      monomial_mul_monomial]
    rfl)
  subst hw'
  have hprod : Poly.product rationalRing r.coefficients (r.check rationalRing L)
      ⟨[(d₁, f₁)]⟩ ⟨[(d₂, f₂)]⟩ =
      (Poly.product rationalRing r.coefficients .value ⟨[(d₁, f₁)]⟩ ⟨[(d₂, f₂)]⟩).bind
        (r.check rationalRing L) := by
    simp only [Poly.product, List.length_singleton, lt_irrefl, ↓reduceIte, Poly.rows,
      bind_eq_bind, bind_bind, bind_value_right]
  have hd : d₁ + d₂ ≤ exponentBound L.maxExponent := by
    have := degree_le_of_check hc
    rwa [degree_single] at this
  unfold PolynomialRing.multiply
  simp only [Poly.degree, List.getLast?_singleton, Option.map_some]
  rw [Checks.checkDegree_of_le L hd]
  simp only [hprod, hw, bind_eq_bind, bind_value, hc]

/-- A sublist of the terms of a canonical polynomial is canonical. -/
private theorem canonical_of_sublist (ha : a.Canonical Rationals.model r.coefficients)
    {l : List (ℕ × Fraction)} (h : l.Sublist a.terms) :
    (⟨l⟩ : Poly Fraction).Canonical Rationals.model r.coefficients := by
  rw [canonical_iff] at ha ⊢
  exact ⟨ha.1.sublist h, fun y hy => ha.2 y (h.subset hy)⟩

/-- The variable `x`, whose check passes. -/
private theorem generator_eq
    (hc : r.check rationalRing L ⟨[(1, Fraction.ofRat 1)]⟩ = .value ⟨[(1, Fraction.ofRat 1)]⟩) :
    r.generator rationalRing L = .value ⟨[(1, Fraction.ofRat 1)]⟩ := by
  have hd : 1 ≤ exponentBound L.maxExponent := by
    have := degree_le_of_check hc
    rwa [degree_single] at this
  unfold PolynomialRing.generator Poly.monomial
  rw [Checks.checkDegree_of_le L hd, ← ofRat_one,
    appendNonzero_of_ne_zero (M := Rationals.model) rationalRing_exact.2 _ 1 (ofRat_reduced 1)
      (by simp [Rationals.model]),
    append_of_lt _ (by simp [Poly.zero])]
  simpa [Poly.zero] using hc

/-- The product `xⁱ xʲ`, whose check passes. -/
private theorem multiply_xpow {i j : ℕ}
    (hc : r.check rationalRing L ⟨[(i + j, Fraction.ofRat 1)]⟩ =
      .value ⟨[(i + j, Fraction.ofRat 1)]⟩) :
    r.multiply rationalRing L ⟨[(i, Fraction.ofRat 1)]⟩ ⟨[(j, Fraction.ofRat 1)]⟩ =
      .value ⟨[(i + j, Fraction.ofRat 1)]⟩ := by
  have e : Fraction.ofRat ((Fraction.ofRat 1).interpret * (Fraction.ofRat 1).interpret) =
      Fraction.ofRat 1 := by rw [ofRat_interpret, mul_one]
  have := multiply_single (r := r) (L := L) (d₁ := i) (d₂ := j) (ofRat_reduced 1) (by simp)
    (ofRat_reduced 1) (by simp) (by rw [e]; exact hc)
  rwa [e] at this

/-- The digits read after `j` give at least `j`. -/
private theorem le_foldl : ∀ (ds : List Bool) (j : ℕ), j ≤ ds.foldl (fun m b => 2 * m + b.toNat) j
  | [], _ => le_rfl
  | b :: ds, j => by
    rw [List.foldl_cons]
    exact le_trans (by omega) (le_foldl ds _)

/-- The loop of a power of `x` by repeated squaring, every intermediate power
at most a degree of `a`. -/
private theorem power_loop (ha : a.Canonical Rationals.model r.coefficients)
    (hcheck : r.check rationalRing L a = .value a) {d : ℕ} {f : Fraction} (hy : (d, f) ∈ a.terms) :
    ∀ (ds : List Bool) (j : ℕ), 1 ≤ j → ds.foldl (fun m b => 2 * m + b.toNat) j ≤ d →
      (ds.foldlM (init := (⟨[(j, Fraction.ofRat 1)]⟩ : Poly Fraction))
          fun (s : Poly Fraction) (digit : Bool) => do
            let s ← r.multiply rationalRing L s s
            if digit then r.multiply rationalRing L s ⟨[(1, Fraction.ofRat 1)]⟩ else pure s) =
        .value ⟨[(ds.foldl (fun m b => 2 * m + b.toNat) j, Fraction.ofRat 1)]⟩ := by
  intro ds
  induction ds with
  | nil => intro j _ _; rfl
  | cons b ds ih =>
    intro j hj hle
    rw [List.foldl_cons] at hle ⊢
    have h2 := le_foldl ds (2 * j + b.toNat)
    have hsq : r.multiply rationalRing L ⟨[(j, Fraction.ofRat 1)]⟩ ⟨[(j, Fraction.ofRat 1)]⟩ =
        .value ⟨[(2 * j, Fraction.ofRat 1)]⟩ := by
      rw [two_mul]
      exact multiply_xpow (check_power ha hcheck hy (by omega) (by omega))
    rw [List.foldlM_cons]
    cases b with
    | false =>
      rw [Bool.toNat_false, add_zero] at hle h2 ⊢
      simp only [bind_eq_bind, hsq, bind_value, Bool.false_eq_true, ↓reduceIte, pure_eq_value]
      exact ih (2 * j) (by omega) hle
    | true =>
      rw [Bool.toNat_true] at hle h2 ⊢
      have hx : r.multiply rationalRing L ⟨[(2 * j, Fraction.ofRat 1)]⟩ ⟨[(1, Fraction.ofRat 1)]⟩ =
          .value ⟨[(2 * j + 1, Fraction.ofRat 1)]⟩ :=
        multiply_xpow (check_power ha hcheck hy (by omega) (by omega))
      simp only [bind_eq_bind, hsq, bind_value, ↓reduceIte, hx]
      exact ih (2 * j + 1) (by omega) hle

/-- The power `xᵈ` for a term `c xᵈ` of `a`. -/
private theorem power_xpow (ha : a.Canonical Rationals.model r.coefficients)
    (hcheck : r.check rationalRing L a = .value a) {d : ℕ} {f : Fraction} (hy : (d, f) ∈ a.terms)
    (hd : 1 ≤ d) :
    r.power rationalRing L ⟨[(1, Fraction.ofRat 1)]⟩ d = .value ⟨[(d, Fraction.ofRat 1)]⟩ := by
  have hb : d ≤ exponentBound L.maxExponent :=
    (le_degree ha hy).trans (degree_le_of_check hcheck)
  unfold PolynomialRing.power
  rw [Checks.checkDegree_of_le L hb, degree_single, mul_one, Checks.checkDegree_of_le L hb]
  simp only [show d ≠ 0 by omega, ↓reduceIte]
  obtain ⟨ds, hds, hval⟩ := Checks.binaryDigits_of_pos (show 0 < d by omega)
  rw [hds, List.tail_cons, power_loop ha hcheck hy ds 1 le_rfl hval.le, hval, bind_eq_bind,
    bind_value]
  exact check_power ha hcheck hy hd le_rfl

/-- The term of the variable to a degree of `a` expands into the power. -/
private theorem expandNode_core (ha : a.Canonical Rationals.model r.coefficients)
    (hcheck : r.check rationalRing L a = .value a) {d : ℕ} {f : Fraction} (hy : (d, f) ∈ a.terms)
    (hd : 1 ≤ d) :
    r.expandNode L (core r.variableName d) = .value ⟨[(d, Fraction.ofRat 1)]⟩ := by
  have hgen := generator_eq (check_power ha hcheck hy le_rfl hd)
  unfold core
  split
  · rename_i h1
    subst h1
    simp [PolynomialRing.expandNode, hgen]
  · have hk : ¬ (d : ℤ) < 0 := by omega
    simp only [PolynomialRing.expandNode, ↓reduceIte, hgen, bind_eq_bind, bind_value, hk,
      Int.toNat_natCast]
    exact power_xpow ha hcheck hy hd

/-- The constant of the coefficient of a term of `a`. -/
private theorem constant_mem (ha : a.Canonical Rationals.model r.coefficients)
    (hcheck : r.check rationalRing L a = .value a) {d : ℕ} {f : Fraction} (hy : (d, f) ∈ a.terms) :
    r.constant rationalRing L (Fraction.ofRat f.interpret) = .value ⟨[(0, f)]⟩ := by
  obtain ⟨hf, hf0⟩ := coeff_of_mem ha hy
  rw [ofRat_interpret_of_reduced hf]
  exact constant_eq hf hf0 (check_const ha hcheck hy)

/-- A term of `a` as the product of its constant and the power of `x`, in
either order. -/
private theorem multiply_term (ha : a.Canonical Rationals.model r.coefficients)
    (hcheck : r.check rationalRing L a = .value a) {d : ℕ} {f : Fraction} (hy : (d, f) ∈ a.terms) :
    r.multiply rationalRing L ⟨[(d, Fraction.ofRat 1)]⟩ ⟨[(0, f)]⟩ = .value ⟨[(d, f)]⟩ ∧
      r.multiply rationalRing L ⟨[(0, f)]⟩ ⟨[(d, Fraction.ofRat 1)]⟩ = .value ⟨[(d, f)]⟩ := by
  obtain ⟨hf, hf0⟩ := coeff_of_mem ha hy
  have hc := check_sublist ha hcheck (List.singleton_sublist.2 hy)
  have e₁ : Fraction.ofRat ((Fraction.ofRat 1).interpret * f.interpret) = f := by
    rw [ofRat_interpret, one_mul, ofRat_interpret_of_reduced hf]
  have e₂ : Fraction.ofRat (f.interpret * (Fraction.ofRat 1).interpret) = f := by
    rw [ofRat_interpret, mul_one, ofRat_interpret_of_reduced hf]
  have h₁ := multiply_single (r := r) (L := L) (d₁ := d) (d₂ := 0) (ofRat_reduced 1) (by simp) hf
    hf0 (by rw [e₁, add_zero]; exact hc)
  have h₂ := multiply_single (r := r) (L := L) (d₁ := 0) (d₂ := d) hf hf0 (ofRat_reduced 1)
    (by simp) (by rw [e₂, zero_add]; exact hc)
  rw [e₁, add_zero] at h₁
  rw [e₂, zero_add] at h₂
  exact ⟨h₁, h₂⟩

/-- The sum of the first terms of `a` and the next one. -/
private theorem add_prefix (ha : a.Canonical Rationals.model r.coefficients)
    (hcheck : r.check rationalRing L a = .value a) {pre rest : List (ℕ × Fraction)}
    {y : ℕ × Fraction} (h : pre ++ y :: rest = a.terms) :
    r.add rationalRing L ⟨pre⟩ ⟨[y]⟩ = .value ⟨pre ++ [y]⟩ := by
  have h' : pre ++ [y] ++ rest = a.terms := by rw [← h]; simp
  have hsub : (pre ++ [y]).Sublist a.terms := h' ▸ List.sublist_append_left _ _
  have hpre : pre.Sublist a.terms := (List.sublist_append_left pre [y]).trans hsub
  have hy : [y].Sublist a.terms := (List.sublist_append_right pre [y]).trans hsub
  obtain ⟨t, ht, htc, hti⟩ :=
    sum_spec rationalRing_exact (canonical_of_sublist ha hpre) (canonical_of_sublist ha hy)
  have htt : t = ⟨pre ++ [y]⟩ :=
    eq_of_interpret_eq Rationals.model r.coefficients (rationalRing_exact.1.unique _) htc
      (canonical_of_sublist ha hsub) (by rw [hti, interpret_append])
  unfold PolynomialRing.add
  rw [ht, bind_eq_bind, bind_value, htt]
  exact check_sublist ha hcheck hsub

/-- The monomials of the terms of `a` after its first terms, expanded and
added to the sum of the first terms. -/
private theorem expandMonomials_prefix (ha : a.Canonical Rationals.model r.coefficients)
    (hcheck : r.check rationalRing L a = .value a) :
    ∀ (rest pre : List (ℕ × Fraction)), pre ++ rest = a.terms → (∀ y ∈ rest, y.1 ≠ 0) →
      PolynomialRing.expandMonomials L r ⟨pre⟩ (monos r.variableName rest) = .value a := by
  intro rest
  induction rest with
  | nil =>
    intro pre h _
    rw [List.append_nil] at h
    simp only [monos, List.map_nil, PolynomialRing.expandMonomials, h]
  | cons y rest ih =>
    intro pre h hpos
    obtain ⟨d, f⟩ := y
    have hy : (d, f) ∈ a.terms := h ▸ List.mem_append_right _ List.mem_cons_self
    have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (hpos _ List.mem_cons_self)
    simp only [monos, List.map_cons, PolynomialRing.expandMonomials, bind_eq_bind,
      expandNode_core ha hcheck hy hd, bind_value, constant_mem ha hcheck hy,
      (multiply_term ha hcheck hy).1, add_prefix ha hcheck h]
    exact ih (pre ++ [(d, f)]) (by rw [← h]; simp) fun y hy => hpos y (List.mem_cons_of_mem _ hy)

/-- The product of the coefficient of a term of `a` and the power of `x`. -/
private theorem expandNode_product (ha : a.Canonical Rationals.model r.coefficients)
    (hcheck : r.check rationalRing L a = .value a) {d : ℕ} {f : Fraction} (hy : (d, f) ∈ a.terms)
    (hd : 1 ≤ d) :
    r.expandNode L (.product f.interpret [core r.variableName d]) = .value ⟨[(d, f)]⟩ := by
  simp only [PolynomialRing.expandNode, bind_eq_bind, constant_mem ha hcheck hy, bind_value,
    PolynomialRing.expandFactors, expandNode_core ha hcheck hy hd, (multiply_term ha hcheck hy).2]

end Steps

private theorem assembleSum_sum {c : ℚ} (hc : c ≠ 0) {ms : List (ℚ × Term)} (h : ms ≠ []) :
    assembleSum c ms = .sum c ms := by
  rcases ms with _ | ⟨m, _ | ⟨m', ms⟩⟩
  · exact absurd rfl h
  · simp [assembleSum, hc]
  · rfl

private theorem coreFactors_core (s : String) (d : ℕ) : (core s d).coreFactors = [core s d] := by
  unfold core
  split <;> rfl

/-- The conversion of a canonical polynomial back to a term expands into the
polynomial, under limits that admit the polynomial and the depth of the
term. -/
public theorem toTerm_expand {o : Orders} (ho : o.Total) {L : Limits}
    {r : PolynomialRing Rationals} {a : Poly Fraction}
    (ha : a.Canonical Rationals.model r.coefficients) {u : Term} (h : r.toTerm o L a = .value u)
    (hdepth : u.depth ≤ L.maxDepth) (hcheck : r.check rationalRing L a = .value a) :
    r.expand L u = .value a := by
  obtain ⟨-, ts, hts, hsum⟩ := toTerm_parts h
  have hb : ∀ y ∈ a.terms, y.2.interpret ≠ 0 ∧ y.1 ≤ exponentBound L.maxExponent :=
    fun y hy => ⟨(coeff_of_mem ha hy).2, (le_degree ha hy).trans (degree_le_of_check hcheck)⟩
  rw [mapM_eq o r.variableName a.terms hb] at hts
  cases hts
  have hnc : (a.terms.map (mono r.variableName)).any Term.isCondition = false := by
    simp [mono_not_condition]
  have hpw := ((canonical_iff _ _ a).1 ha).1
  have hu : r.expand L u = r.expandNode L u := by
    simp [PolynomialRing.expand, not_lt.2 hdepth]
  rw [hu]
  obtain ⟨l⟩ := a
  simp only at hb hnc hpw hsum
  rcases l with _ | ⟨⟨d, f⟩, rest⟩
  · rw [mkSum_monos ho r.variableName 0 [] (by simp) (by simp) (by simp) _ hnc rfl] at hsum
    cases hsum
    show r.expandNode L (.number 0) = _
    simp only [PolynomialRing.expandNode]
    exact constant_zero hcheck
  · have hrest : ∀ y ∈ rest, y.1 ≠ 0 := by
      intro y hy
      have := (List.pairwise_cons.1 hpw).1 y hy
      simp only at this
      omega
    have hf := coeff_of_mem ha (y := (d, f)) List.mem_cons_self
    have hc : ∀ y ∈ rest, y.2.interpret ≠ 0 := fun y hy => (hb y (List.mem_cons_of_mem _ hy)).1
    by_cases hd : d = 0
    · subst hd
      have hparts : sumParts (((0, f) :: rest).map (mono r.variableName)) =
          (f.interpret, monos r.variableName rest) := by
        simp [mono, sumParts, sumParts_monos _ rest hrest]
      rw [mkSum_monos ho _ _ rest (List.pairwise_cons.1 hpw).2 hrest hc _ hnc hparts] at hsum
      cases hsum
      rcases rest with _ | ⟨y, rest⟩
      · show r.expandNode L (.number f.interpret) = _
        simp only [PolynomialRing.expandNode]
        exact constant_mem ha hcheck List.mem_cons_self
      · rw [assembleSum_sum hf.2 (by simp [monos])]
        simp only [PolynomialRing.expandNode, bind_eq_bind, constant_mem ha hcheck List.mem_cons_self,
          bind_value]
        exact expandMonomials_prefix ha hcheck (y :: rest) [(0, f)] rfl hrest
    · have hall : ∀ y ∈ (d, f) :: rest, y.1 ≠ 0 := by
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hd
        · exact hrest y hy
      have hc' : ∀ y ∈ (d, f) :: rest, y.2.interpret ≠ 0 := fun y hy => (hb y hy).1
      rw [mkSum_monos ho _ 0 _ hpw hall hc' _ hnc (sumParts_monos _ _ hall)] at hsum
      cases hsum
      have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 hd
      rcases rest with _ | ⟨y, rest⟩
      · by_cases hq : f.interpret = 1
        · simp only [monos, List.map_cons, List.map_nil, assembleSum, hq, ↓reduceIte]
          rw [expandNode_core ha hcheck List.mem_cons_self hd1, ← hq, ofRat_interpret_of_reduced hf.1]
        · simp only [monos, List.map_cons, List.map_nil, assembleSum, hq, ↓reduceIte,
            coreFactors_core]
          exact expandNode_product ha hcheck List.mem_cons_self hd1
      · show r.expandNode L (.sum 0 (monos r.variableName ((d, f) :: y :: rest))) = _
        simp only [PolynomialRing.expandNode, bind_eq_bind,
          constant_zero (check_sublist ha hcheck (List.nil_sublist _)), bind_value]
        exact expandMonomials_prefix ha hcheck _ [] rfl hall

end Kalyx.Proofs.Polynomials.Roundtrip
