module

public import Kalyx.Statements.Terms

/-!
# Sorting and merging

Lemmas about sorting and merging that the proofs of the canonical forms use:
sorting by insertion (`insertBy`, `sortBy`) permutes a list and sorts it,
strictly increasing lists (`strictlyIncreasing`) are determined by their
elements, and merging the adjacent elements of one key (`mergeAdjacent`)
keeps the keys and the total weight of each key. Their instances are the
merging of monomials by core (`mergeMonomials`), of the items of a product by
key (`mergeItems`), and the sorted lists of terms (`sortedTerms`,
`maxBases`).

The orders are hypotheses (`TotalCmp`, `Std.TransCmp`), so that these lemmas
do not depend on the proof that the order of terms is total.
-/

namespace Kalyx.Proofs.Terms

open Kalyx.Spec.Terms Kalyx.Statements.Terms

variable {α β : Type}

/-! ## Sorting by insertion -/

/-- In a transitive order, not being above another element is transitive. -/
private theorem ne_gt_trans {c : α → α → Ordering} [Std.TransCmp c] {a b d : α}
    (h₁ : c a b ≠ .gt) (h₂ : c b d ≠ .gt) : c a d ≠ .gt :=
  Ordering.isLE_iff_ne_gt.1
    (Std.TransCmp.isLE_trans (Ordering.isLE_iff_ne_gt.2 h₁) (Ordering.isLE_iff_ne_gt.2 h₂))

/-- The order `c` on the keys `f` of the elements is transitive when `c` is. -/
public theorem transCmp_comp {c : β → β → Ordering} [Std.TransCmp c] (f : α → β) :
    Std.TransCmp fun a b => c (f a) (f b) :=
  { eq_swap := Std.OrientedCmp.eq_swap, isLE_trans := Std.TransCmp.isLE_trans }

/-- Inserting `x` into `l` permutes `x :: l`. -/
public theorem perm_insertBy (c : α → α → Ordering) (x : α) (l : List α) :
    (insertBy c x l).Perm (x :: l) := by
  induction l with
  | nil => simp [insertBy]
  | cons y ys ih =>
    simp only [insertBy]; split
    · exact (ih.cons y).trans (List.Perm.swap x y ys)
    · exact List.Perm.refl _

/-- Sorting permutes the list. -/
public theorem perm_sortBy (c : α → α → Ordering) (l : List α) : (sortBy c l).Perm l := by
  induction l with
  | nil => simp [sortBy]
  | cons x xs ih => simpa only [sortBy] using (perm_insertBy c x _).trans (ih.cons x)

/-- Inserting into a list sorted by a transitive order keeps it sorted. -/
public theorem pairwise_insertBy {c : α → α → Ordering} [Std.TransCmp c] {x : α} {l : List α}
    (h : l.Pairwise fun a b => c a b ≠ .gt) :
    (insertBy c x l).Pairwise fun a b => c a b ≠ .gt := by
  induction l with
  | nil => simp [insertBy]
  | cons y ys ih =>
    rw [List.pairwise_cons] at h
    simp only [insertBy]; split
    · rename_i hxy
      refine List.pairwise_cons.2 ⟨fun z hz => ?_, ih h.2⟩
      rcases List.mem_cons.1 ((perm_insertBy c x ys).mem_iff.1 hz) with rfl | hz
      · simp [Std.OrientedCmp.lt_of_gt (beq_iff_eq.1 hxy)]
      · exact h.1 z hz
    · rename_i hxy
      have hxy : c x y ≠ .gt := by simpa using hxy
      refine List.pairwise_cons.2 ⟨fun z hz => ?_, List.pairwise_cons.2 h⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hxy
      · exact ne_gt_trans hxy (h.1 z hz)

/-- A list sorted by a transitive order: no element is above a later one. -/
public theorem pairwise_sortBy (c : α → α → Ordering) [Std.TransCmp c] (l : List α) :
    (sortBy c l).Pairwise fun a b => c a b ≠ .gt := by
  induction l with
  | nil => simp [sortBy]
  | cons x xs ih => simpa only [sortBy] using pairwise_insertBy ih

/-- Inserting an element `eq` to none of a strictly increasing list keeps it so. -/
public theorem pairwise_lt_insertBy {c : α → α → Ordering} [Std.TransCmp c] {x : α} {l : List α}
    (h : l.Pairwise fun a b => c a b = .lt) (hx : ∀ y ∈ l, c x y ≠ .eq) :
    (insertBy c x l).Pairwise fun a b => c a b = .lt := by
  induction l with
  | nil => simp [insertBy]
  | cons y ys ih =>
    rw [List.pairwise_cons] at h
    simp only [insertBy]; split
    · rename_i hxy
      refine List.pairwise_cons.2
        ⟨fun z hz => ?_, ih h.2 fun z hz => hx z (List.mem_cons_of_mem _ hz)⟩
      rcases List.mem_cons.1 ((perm_insertBy c x ys).mem_iff.1 hz) with rfl | hz
      · exact Std.OrientedCmp.lt_of_gt (beq_iff_eq.1 hxy)
      · exact h.1 z hz
    · rename_i hxy
      have hlt : c x y = .lt := by
        cases e : c x y
        · rfl
        · exact absurd e (hx y List.mem_cons_self)
        · simp [e] at hxy
      refine List.pairwise_cons.2 ⟨fun z hz => ?_, List.pairwise_cons.2 h⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hlt
      · exact Std.TransCmp.lt_trans hlt (h.1 z hz)

/-! ## Strictly increasing lists -/

/-- `strictlyIncreasing` of a list of at least two elements. -/
private theorem strictlyIncreasing_cons_cons {c : α → α → Ordering} {a b : α} {l : List α} :
    strictlyIncreasing c (a :: b :: l) = ((c a b == .lt) && strictlyIncreasing c (b :: l)) := by
  rw [strictlyIncreasing]

/-- Strictly increasing in a transitive order: each element below every later one. -/
public theorem strictlyIncreasing_iff_pairwise {c : α → α → Ordering} [Std.TransCmp c]
    {l : List α} : strictlyIncreasing c l = true ↔ l.Pairwise fun a b => c a b = .lt := by
  induction l with
  | nil => simp [strictlyIncreasing]
  | cons x xs ih =>
    rcases xs with _ | ⟨y, ys⟩
    · simp [strictlyIncreasing]
    · rw [strictlyIncreasing_cons_cons, Bool.and_eq_true, ih, beq_iff_eq]
      constructor
      · rintro ⟨h1, h2⟩
        refine List.pairwise_cons.2 ⟨fun z hz => ?_, h2⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · exact h1
        · exact Std.TransCmp.lt_trans h1 ((List.pairwise_cons.1 h2).1 z hz)
      · intro h
        exact ⟨(List.pairwise_cons.1 h).1 y List.mem_cons_self, (List.pairwise_cons.1 h).2⟩

/-- Keys `f` strictly increasing: each element below every later one by key. -/
public theorem pairwise_of_strictlyIncreasing_map {c : β → β → Ordering} [Std.TransCmp c]
    {f : α → β} {l : List α} (h : strictlyIncreasing c (l.map f) = true) :
    l.Pairwise fun a b => c (f a) (f b) = .lt :=
  List.pairwise_map.1 (strictlyIncreasing_iff_pairwise.1 h)

/-- A filter keeps the keys `f` of a list strictly increasing. -/
public theorem strictlyIncreasing_filter_map {c : β → β → Ordering} [Std.TransCmp c]
    {f : α → β} {l : List α} (h : strictlyIncreasing c (l.map f) = true) (p : α → Bool) :
    strictlyIncreasing c ((l.filter p).map f) = true :=
  strictlyIncreasing_iff_pairwise.2
    (List.pairwise_map.2 ((pairwise_of_strictlyIncreasing_map h).filter p))

/-- A list that increases strictly in an oriented order has no repetitions. -/
public theorem nodup_of_pairwise_lt {c : α → α → Ordering} [Std.OrientedCmp c] {l : List α}
    (h : l.Pairwise fun a b => c a b = .lt) : l.Nodup :=
  h.imp fun hab e => by subst e; rw [Std.ReflCmp.compare_self (cmp := c)] at hab; cases hab

/-- Two strictly increasing lists in an oriented order with the same elements. -/
public theorem eq_of_pairwise_lt {c : α → α → Ordering} [Std.OrientedCmp c] {l l' : List α}
    (h : l.Pairwise fun a b => c a b = .lt) (h' : l'.Pairwise fun a b => c a b = .lt)
    (hm : ∀ x, x ∈ l ↔ x ∈ l') : l = l' := by
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => rfl
    | cons y _ => simpa using (hm y).2 List.mem_cons_self
  | cons x xs ih =>
    cases l' with
    | nil => simpa using (hm x).1 List.mem_cons_self
    | cons y ys =>
      rw [List.pairwise_cons] at h h'
      have irr : ∀ {a b}, c a b = .lt → b ≠ a := fun hab e => by
        subst e; rw [Std.ReflCmp.compare_self (cmp := c)] at hab; cases hab
      have hxy : x = y := by
        rcases List.mem_cons.1 ((hm x).1 List.mem_cons_self) with e | hx
        · exact e
        rcases List.mem_cons.1 ((hm y).2 List.mem_cons_self) with e | hy
        · exact e.symm
        have := Std.OrientedCmp.gt_of_lt (h'.1 x hx)
        rw [h.1 y hy] at this
        cases this
      subst hxy
      have hm' : ∀ z, z ∈ xs ↔ z ∈ ys := fun z =>
        ⟨fun hz => (List.mem_cons.1 ((hm z).1 (List.mem_cons_of_mem _ hz))).resolve_left
            (irr (h.1 z hz)),
          fun hz => (List.mem_cons.1 ((hm z).2 (List.mem_cons_of_mem _ hz))).resolve_left
            (irr (h'.1 z hz))⟩
      rw [ih h.2 h'.2 hm']

/-- Two strictly increasing lists in a total order with the same elements. -/
public theorem eq_of_strictlyIncreasing {c : α → α → Ordering} (hc : TotalCmp c)
    {l l' : List α} (h : strictlyIncreasing c l = true) (h' : strictlyIncreasing c l' = true)
    (hm : ∀ x, x ∈ l ↔ x ∈ l') : l = l' :=
  have := hc.1
  eq_of_pairwise_lt (strictlyIncreasing_iff_pairwise.1 h) (strictlyIncreasing_iff_pairwise.1 h') hm

/-- Two lists with strictly increasing keys `f` and the same elements. -/
public theorem eq_of_strictlyIncreasing_map {c : β → β → Ordering} [Std.TransCmp c] (f : α → β)
    {l l' : List α} (h : strictlyIncreasing c (l.map f) = true)
    (h' : strictlyIncreasing c (l'.map f) = true) (hm : ∀ x, x ∈ l ↔ x ∈ l') : l = l' :=
  have := transCmp_comp (c := c) f
  eq_of_pairwise_lt (pairwise_of_strictlyIncreasing_map h)
    (pairwise_of_strictlyIncreasing_map h') hm

/-- Sorting by distinct keys `f` in a total order gives strictly increasing keys. -/
public theorem strictlyIncreasing_sortBy_map {c : β → β → Ordering} (hc : TotalCmp c) (f : α → β)
    {l : List α} (hl : (l.map f).Nodup) :
    strictlyIncreasing c ((sortBy (fun a b => c (f a) (f b)) l).map f) = true := by
  have := hc.1; have := hc.2; have := transCmp_comp (c := c) f
  have hnd : ((sortBy (fun a b => c (f a) (f b)) l).map f).Nodup :=
    ((perm_sortBy _ l).map f).nodup_iff.2 hl
  rw [strictlyIncreasing_iff_pairwise, List.pairwise_map]
  refine ((pairwise_sortBy _ l).and (List.pairwise_map.1 hnd)).imp fun {a b} ⟨h1, h2⟩ => ?_
  cases e : c (f a) (f b)
  · rfl
  · exact absurd (Std.LawfulEqCmp.eq_of_compare e) h2
  · exact absurd e h1

/-- Inserting an element of a new key `f` keeps the keys strictly increasing. -/
public theorem strictlyIncreasing_insertBy_map {c : β → β → Ordering} (hc : TotalCmp c)
    (f : α → β) {x : α} {l : List α} (hl : strictlyIncreasing c (l.map f) = true)
    (hx : f x ∉ l.map f) :
    strictlyIncreasing c ((insertBy (fun a b => c (f a) (f b)) x l).map f) = true := by
  have := hc.1; have := hc.2; have := transCmp_comp (c := c) f
  rw [strictlyIncreasing_iff_pairwise, List.pairwise_map]
  refine pairwise_lt_insertBy (pairwise_of_strictlyIncreasing_map hl) fun y hy e => hx ?_
  rw [Std.LawfulEqCmp.eq_of_compare e]
  exact List.mem_map.2 ⟨y, hy, rfl⟩

/-! ## Merging adjacent elements of one key -/

section Merge

variable {M : Type} [AddCommMonoid M] [DecidableEq β]

/-- The total weight of the elements of the key `k` of `a :: l`. -/
private theorem sum_filter_cons (f : α → β) (w : α → M) (a : α) (l : List α) (k : β) :
    (((a :: l).filter fun x => f x = k).map w).sum =
      (if f a = k then w a else 0) + ((l.filter fun x => f x = k).map w).sum := by
  by_cases h : f a = k <;> simp [h]

/-- Without repeated keys, the total weight of the key of an element is its own. -/
private theorem sum_filter_of_nodup (f : α → β) (w : α → M) {r : List α}
    (hr : (r.map f).Nodup) {m : α} (hm : m ∈ r) :
    ((r.filter fun x => f x = f m).map w).sum = w m := by
  induction r with
  | nil => cases hm
  | cons a as ih =>
    rw [List.map_cons, List.nodup_cons] at hr
    rcases List.mem_cons.1 hm with rfl | hm
    · rw [List.filter_cons_of_pos (by simp), List.filter_eq_nil_iff.2 ?_]
      · simp
      · intro x hx e
        exact hr.1 (List.mem_map.2 ⟨x, hx, of_decide_eq_true e⟩)
    · have hne : f a ≠ f m := fun e => hr.1 (by rw [e]; exact List.mem_map.2 ⟨m, hm, rfl⟩)
      rw [List.filter_cons_of_neg (by simpa using hne)]
      exact ih hr.2 hm

/-- Without repeated keys, the elements are those whose key occurs with their
weight as the total, when an element is determined by its key and weight. -/
private theorem mem_iff_of_nodup (f : α → β) (w : α → M)
    (hinj : ∀ x y, f x = f y → w x = w y → x = y) {l : List α} (hl : (l.map f).Nodup)
    {m : α} : m ∈ l ↔ f m ∈ l.map f ∧ w m = ((l.filter fun x => f x = f m).map w).sum := by
  refine ⟨fun hm => ⟨List.mem_map.2 ⟨m, hm, rfl⟩, (sum_filter_of_nodup f w hl hm).symm⟩, ?_⟩
  rintro ⟨hk, hw⟩
  obtain ⟨m', hm', e⟩ := List.mem_map.1 hk
  rwa [← hinj m' m e (by rw [← sum_filter_of_nodup f w hl hm', e, hw])]

/-- Merging a list sorted by key `f`, where elements of one key join into one of
that key and of the sum of their weights `w`, gives strictly increasing keys,
the same keys, and the same total weight of each key. -/
private theorem merge_spec {c : β → β → Ordering} (hc : ∀ a b, c a b = .eq → a = b)
    (f : α → β) (w : α → M) (J : α → α → Option α)
    (hs : ∀ x y z, J x y = some z → f x = f y ∧ f z = f x ∧ w z = w x + w y)
    (hn : ∀ x y, J x y = none → f x ≠ f y) (l : List α)
    (hl : l.Pairwise fun a b => c (f a) (f b) ≠ .gt) :
    strictlyIncreasing c ((mergeAdjacent J l).map f) = true ∧
      (∀ k, k ∈ (mergeAdjacent J l).map f ↔ k ∈ l.map f) ∧
      ∀ k, (((mergeAdjacent J l).filter fun x => f x = k).map w).sum =
        ((l.filter fun x => f x = k).map w).sum := by
  induction l with
  | nil => simp [mergeAdjacent, strictlyIncreasing]
  | cons x rest ih =>
    rw [List.pairwise_cons] at hl
    obtain ⟨ih1, ih2, ih3⟩ := ih hl.2
    simp only [mergeAdjacent]
    generalize mergeAdjacent J rest = r' at ih1 ih2 ih3 ⊢
    rcases r' with _ | ⟨y, more⟩
    · cases rest with
      | nil => simp [strictlyIncreasing]
      | cons z zs => exact absurd ((ih2 (f z)).2 (by simp)) (by simp)
    · have hy : c (f x) (f y) ≠ .gt := by
        obtain ⟨z, hz, e⟩ := List.mem_map.1 ((ih2 (f y)).1 (by simp))
        rw [← e]; exact hl.1 z hz
      rcases hJ : J x y with _ | z
      · simp only [hJ]
        have hne := hn x y hJ
        have hlt : c (f x) (f y) = .lt := by
          cases h : c (f x) (f y)
          · rfl
          · exact absurd (hc _ _ h) hne
          · exact absurd h hy
        refine ⟨?_, fun k => ?_, fun k => ?_⟩
        · rw [List.map_cons] at ih1
          rw [List.map_cons, List.map_cons, strictlyIncreasing_cons_cons, hlt, ih1]
          rfl
        · rw [List.map_cons] at ih2
          exact List.mem_cons.trans ((or_congr_right (ih2 k)).trans List.mem_cons.symm)
        · rw [sum_filter_cons f w x (y :: more), sum_filter_cons f w x rest, ih3 k]
      · simp only [hJ]
        obtain ⟨hxy, hfz, hwz⟩ := hs x y z hJ
        have hm : (z :: more).map f = (y :: more).map f := by simp [hfz, hxy]
        refine ⟨by rw [hm]; exact ih1, fun k => ?_, fun k => ?_⟩
        · rw [hm, ih2, List.map_cons, List.mem_cons, or_iff_right_of_imp]
          rintro rfl; rw [hxy]; exact (ih2 _).1 (by simp)
        · rw [sum_filter_cons f w z more, sum_filter_cons f w x rest, ← ih3 k,
            sum_filter_cons f w y more, hfz, ← hxy, hwz]
          by_cases h : f x = k <;> simp [h, add_assoc]

/-- `merge_spec` in a total order, with the elements of the merged list when an
element is determined by its key and its weight. -/
private theorem merge_all {c : β → β → Ordering} (hc : TotalCmp c) (f : α → β) (w : α → M)
    (J : α → α → Option α)
    (hs : ∀ x y z, J x y = some z → f x = f y ∧ f z = f x ∧ w z = w x + w y)
    (hn : ∀ x y, J x y = none → f x ≠ f y) (hinj : ∀ x y, f x = f y → w x = w y → x = y)
    {l : List α} (hl : l.Pairwise fun a b => c (f a) (f b) ≠ .gt) :
    strictlyIncreasing c ((mergeAdjacent J l).map f) = true ∧
      (∀ k, k ∈ (mergeAdjacent J l).map f ↔ k ∈ l.map f) ∧
      (∀ k, (((mergeAdjacent J l).filter fun x => f x = k).map w).sum =
        ((l.filter fun x => f x = k).map w).sum) ∧
      ∀ m, m ∈ mergeAdjacent J l ↔
        f m ∈ l.map f ∧ w m = ((l.filter fun x => f x = f m).map w).sum := by
  have := hc.1; have := hc.2
  obtain ⟨h1, h2, h3⟩ := merge_spec (fun _ _ => Std.LawfulEqCmp.eq_of_compare) f w J hs hn l hl
  refine ⟨h1, h2, h3, fun m => ?_⟩
  rw [mem_iff_of_nodup f w hinj (nodup_of_pairwise_lt (strictlyIncreasing_iff_pairwise.1 h1)),
    h2, h3]

end Merge

/-! ## Monomials -/

/-- Joined monomials have one core, kept, and the sum of their coefficients. -/
private theorem monomial_some (x y z : ℚ × Term)
    (h : (if x.2 = y.2 then some (x.1 + y.1, x.2) else none) = some z) :
    x.2 = y.2 ∧ z.2 = x.2 ∧ z.1 = x.1 + y.1 := by
  split at h <;> cases h; exact ⟨‹_›, rfl, rfl⟩

/-- Two adjacent monomials that stay apart have different cores. -/
private theorem monomial_none (x y : ℚ × Term)
    (h : (if x.2 = y.2 then some (x.1 + y.1, x.2) else none) = none) : x.2 ≠ y.2 :=
  fun e => by rw [ite_eq_left e] at h; cases h

/-- The merging of monomials: cores, coefficients and elements. -/
private theorem mergeMonomials_spec {o : Orders} (hc : TotalCmp (Term.cmp o))
    (ms : List (ℚ × Term)) :
    strictlyIncreasing (Term.cmp o) ((mergeMonomials o ms).map Prod.snd) = true ∧
      (∀ t, t ∈ (mergeMonomials o ms).map Prod.snd ↔ t ∈ ms.map Prod.snd) ∧
      (∀ t, coefficientOf t (mergeMonomials o ms) = coefficientOf t ms) ∧
      ∀ m, m ∈ mergeMonomials o ms ↔ m.2 ∈ ms.map Prod.snd ∧ m.1 = coefficientOf m.2 ms := by
  have := hc.1
  have : Std.TransCmp (monomialCmp o) := transCmp_comp (c := Term.cmp o) Prod.snd
  have hp := perm_sortBy (monomialCmp o) ms
  obtain ⟨h1, h2, h3, h4⟩ := merge_all hc Prod.snd Prod.fst
    (fun m n => if m.2 = n.2 then some (m.1 + n.1, m.2) else none) monomial_some monomial_none
    (fun x y h h' => Prod.ext h' h) (pairwise_sortBy (monomialCmp o) ms)
  refine ⟨h1, fun t => (h2 t).trans (hp.map _).mem_iff,
    fun t => (h3 t).trans ((hp.filter _).map _).sum_eq, fun m => ?_⟩
  have := h4 m; rw [(hp.map _).mem_iff, ((hp.filter _).map _).sum_eq] at this; exact this

/-- The cores of the merged monomials increase strictly in the order of terms. -/
public theorem mergeMonomials_strictlyIncreasing {o : Orders} (hc : TotalCmp (Term.cmp o))
    (ms : List (ℚ × Term)) :
    strictlyIncreasing (Term.cmp o) ((mergeMonomials o ms).map Prod.snd) = true :=
  (mergeMonomials_spec hc ms).1

/-- The merged monomials have the cores of the monomials. -/
public theorem mem_cores_mergeMonomials {o : Orders} (hc : TotalCmp (Term.cmp o))
    (ms : List (ℚ × Term)) (t : Term) :
    t ∈ (mergeMonomials o ms).map Prod.snd ↔ t ∈ ms.map Prod.snd :=
  (mergeMonomials_spec hc ms).2.1 t

/-- The merged monomials have the total coefficient of each core. -/
public theorem coefficientOf_mergeMonomials {o : Orders} (hc : TotalCmp (Term.cmp o))
    (ms : List (ℚ × Term)) (t : Term) :
    coefficientOf t (mergeMonomials o ms) = coefficientOf t ms :=
  (mergeMonomials_spec hc ms).2.2.1 t

/-- The merged monomials are the cores of the monomials with their totals. -/
public theorem mem_mergeMonomials {o : Orders} (hc : TotalCmp (Term.cmp o))
    {ms : List (ℚ × Term)} {m : ℚ × Term} :
    m ∈ mergeMonomials o ms ↔ m.2 ∈ ms.map Prod.snd ∧ m.1 = coefficientOf m.2 ms :=
  (mergeMonomials_spec hc ms).2.2.2 m

/-- The merging of monomials depends only on their cores and coefficients. -/
public theorem mergeMonomials_congr {o : Orders} (hc : TotalCmp (Term.cmp o))
    {ms ms' : List (ℚ × Term)} (hcore : ∀ t, t ∈ ms.map Prod.snd ↔ t ∈ ms'.map Prod.snd)
    (hcoef : ∀ t, coefficientOf t ms = coefficientOf t ms') :
    mergeMonomials o ms = mergeMonomials o ms' :=
  have := hc.1
  eq_of_strictlyIncreasing_map Prod.snd (mergeMonomials_strictlyIncreasing hc ms)
    (mergeMonomials_strictlyIncreasing hc ms') fun m => by
      rw [mem_mergeMonomials hc, mem_mergeMonomials hc, hcore, hcoef]

/-- The merging of monomials does not depend on their order. -/
public theorem mergeMonomials_perm {o : Orders} (hc : TotalCmp (Term.cmp o))
    {ms ms' : List (ℚ × Term)} (hp : ms.Perm ms') : mergeMonomials o ms = mergeMonomials o ms' :=
  mergeMonomials_congr hc (fun _ => (hp.map _).mem_iff) fun _ => ((hp.filter _).map _).sum_eq

/-- Monomials whose cores increase strictly are their own merging. -/
public theorem mergeMonomials_eq_self {o : Orders} (hc : TotalCmp (Term.cmp o))
    {ms : List (ℚ × Term)} (h : strictlyIncreasing (Term.cmp o) (ms.map Prod.snd) = true) :
    mergeMonomials o ms = ms :=
  have := hc.1
  eq_of_strictlyIncreasing_map Prod.snd (mergeMonomials_strictlyIncreasing hc ms) h fun m => by
    rw [mem_mergeMonomials hc]
    exact (mem_iff_of_nodup Prod.snd Prod.fst (fun x y h h' => Prod.ext h' h)
      (nodup_of_pairwise_lt (strictlyIncreasing_iff_pairwise.1 h))).symm

/-! ## Items of products -/

/-- The sum of the exponents of two items of one key keeps the key: their sign
over a base that is not a constant, and no sign over a constant. -/
public theorem key_add {b b' : Term} {k k' : ℤ} (h : Key.of b k = Key.of b' k') :
    Key.of b (k + k') = Key.of b k := by
  have hb : b = b' := congrArg Key.base h
  subst hb
  have hn := congrArg Key.negative h
  simp only [Key.of] at hn ⊢
  congr 1
  by_cases hk : k < 0 <;> by_cases hk' : k' < 0 <;> cases hb : b.isConstant <;> simp_all <;> omega

/-- Joined items have one key, kept, and the sum of their exponents. -/
private theorem item_some (x y z : Term × ℤ)
    (h : (if Key.of x.1 x.2 = Key.of y.1 y.2 then some (x.1, x.2 + y.2) else none) = some z) :
    Key.of x.1 x.2 = Key.of y.1 y.2 ∧ Key.of z.1 z.2 = Key.of x.1 x.2 ∧ z.2 = x.2 + y.2 := by
  split at h <;> cases h; exact ⟨‹_›, key_add ‹_›, rfl⟩

/-- Two adjacent items that stay apart have different keys. -/
private theorem item_none (x y : Term × ℤ)
    (h : (if Key.of x.1 x.2 = Key.of y.1 y.2 then some (x.1, x.2 + y.2) else none) = none) :
    Key.of x.1 x.2 ≠ Key.of y.1 y.2 :=
  fun e => by rw [ite_eq_left e] at h; cases h

/-- An item is determined by its key and its exponent. -/
private theorem item_inj (x y : Term × ℤ) (h : Key.of x.1 x.2 = Key.of y.1 y.2)
    (h' : x.2 = y.2) : x = y :=
  Prod.ext (congrArg Key.base h) h'

/-- The merging of items: keys, exponents and elements. -/
private theorem mergeItems_spec {o : Orders} (hc : TotalCmp (Key.cmp o)) (items : List (Term × ℤ)) :
    strictlyIncreasing (Key.cmp o) ((mergeItems o items).map fun x => Key.of x.1 x.2) = true ∧
      (∀ K, K ∈ (mergeItems o items).map (fun x => Key.of x.1 x.2) ↔
        K ∈ items.map fun x => Key.of x.1 x.2) ∧
      (∀ K, exponentOf K (mergeItems o items) = exponentOf K items) ∧
      ∀ x, x ∈ mergeItems o items ↔ Key.of x.1 x.2 ∈ items.map (fun y => Key.of y.1 y.2) ∧
        x.2 = exponentOf (Key.of x.1 x.2) items := by
  have := hc.1
  have : Std.TransCmp fun x y : Term × ℤ => Key.cmp o (Key.of x.1 x.2) (Key.of y.1 y.2) :=
    transCmp_comp (c := Key.cmp o) fun x : Term × ℤ => Key.of x.1 x.2
  have hp := perm_sortBy (fun x y : Term × ℤ => Key.cmp o (Key.of x.1 x.2) (Key.of y.1 y.2)) items
  obtain ⟨h1, h2, h3, h4⟩ := merge_all hc (fun x : Term × ℤ => Key.of x.1 x.2) Prod.snd
    (fun x y => if Key.of x.1 x.2 = Key.of y.1 y.2 then some (x.1, x.2 + y.2) else none)
    item_some item_none item_inj (pairwise_sortBy _ items)
  refine ⟨h1, fun K => (h2 K).trans (hp.map _).mem_iff,
    fun K => (h3 K).trans ((hp.filter _).map _).sum_eq, fun x => ?_⟩
  have := h4 x; rw [(hp.map _).mem_iff, ((hp.filter _).map _).sum_eq] at this; exact this

/-- The keys of the merged items increase strictly in the order of keys. -/
public theorem mergeItems_strictlyIncreasing {o : Orders} (hc : TotalCmp (Key.cmp o))
    (items : List (Term × ℤ)) :
    strictlyIncreasing (Key.cmp o) ((mergeItems o items).map fun x => Key.of x.1 x.2) = true :=
  (mergeItems_spec hc items).1

/-- The merged items have the keys of the items. -/
public theorem mem_keys_mergeItems {o : Orders} (hc : TotalCmp (Key.cmp o))
    (items : List (Term × ℤ)) (K : Key) :
    K ∈ (mergeItems o items).map (fun x => Key.of x.1 x.2) ↔
      K ∈ items.map fun x => Key.of x.1 x.2 :=
  (mergeItems_spec hc items).2.1 K

/-- The merged items have the total exponent of each key of the items. -/
public theorem exponentOf_mergeItems {o : Orders} (hc : TotalCmp (Key.cmp o))
    (items : List (Term × ℤ)) (K : Key) :
    exponentOf K (mergeItems o items) = exponentOf K items :=
  (mergeItems_spec hc items).2.2.1 K

/-- The merged items are the keys of the items, each with its total exponent. -/
public theorem mem_mergeItems {o : Orders} (hc : TotalCmp (Key.cmp o))
    {items : List (Term × ℤ)} {x : Term × ℤ} :
    x ∈ mergeItems o items ↔ Key.of x.1 x.2 ∈ items.map (fun y => Key.of y.1 y.2) ∧
      x.2 = exponentOf (Key.of x.1 x.2) items :=
  (mergeItems_spec hc items).2.2.2 x

/-- The total exponent of a key of the items, on its base, has that key. -/
public theorem key_exponentOf {o : Orders} (hc : TotalCmp (Key.cmp o)) {items : List (Term × ℤ)}
    {K : Key} (hK : K ∈ items.map fun x => Key.of x.1 x.2) :
    Key.of K.base (exponentOf K items) = K := by
  obtain ⟨x, hx, e⟩ := List.mem_map.1 ((mem_keys_mergeItems (o := o) hc items K).2 hK)
  have h2 := ((mem_mergeItems hc).1 hx).2
  subst e; rw [← h2]; rfl

/-- The merging of items depends only on their keys and total exponents. -/
public theorem mergeItems_congr {o : Orders} (hc : TotalCmp (Key.cmp o))
    {items items' : List (Term × ℤ)}
    (hkey : ∀ K, K ∈ items.map (fun x => Key.of x.1 x.2) ↔ K ∈ items'.map fun x => Key.of x.1 x.2)
    (hexp : ∀ K, exponentOf K items = exponentOf K items') :
    mergeItems o items = mergeItems o items' :=
  have := hc.1
  eq_of_strictlyIncreasing_map (fun x : Term × ℤ => Key.of x.1 x.2)
    (mergeItems_strictlyIncreasing hc items) (mergeItems_strictlyIncreasing hc items') fun x => by
      rw [mem_mergeItems hc, mem_mergeItems hc, hkey, hexp]

/-- The merging of items does not depend on their order. -/
public theorem mergeItems_perm {o : Orders} (hc : TotalCmp (Key.cmp o))
    {items items' : List (Term × ℤ)} (hp : items.Perm items') :
    mergeItems o items = mergeItems o items' :=
  mergeItems_congr hc (fun _ => (hp.map _).mem_iff) fun _ => ((hp.filter _).map _).sum_eq

/-- Items whose keys increase strictly are their own merging. -/
public theorem mergeItems_eq_self {o : Orders} (hc : TotalCmp (Key.cmp o))
    {items : List (Term × ℤ)}
    (h : strictlyIncreasing (Key.cmp o) (items.map fun x => Key.of x.1 x.2) = true) :
    mergeItems o items = items :=
  have := hc.1
  eq_of_strictlyIncreasing_map (fun x : Term × ℤ => Key.of x.1 x.2)
    (mergeItems_strictlyIncreasing hc items) h fun x => by
      rw [mem_mergeItems hc]
      exact (mem_iff_of_nodup (fun x : Term × ℤ => Key.of x.1 x.2) Prod.snd item_inj
        (nodup_of_pairwise_lt (strictlyIncreasing_iff_pairwise.1 h))).symm

/-! ## Sorted lists of terms and maximal bases -/

/-- Two adjacent equal terms join into one. -/
private theorem term_some (x y z : Term) (h : (if x = y then some x else none) = some z) :
    x = y ∧ z = x ∧ (0 : ℕ) = 0 + 0 := by
  split at h <;> cases h; exact ⟨‹_›, rfl, rfl⟩

/-- Two adjacent terms that stay apart are different. -/
private theorem term_none (x y : Term) (h : (if x = y then some x else none) = none) : x ≠ y :=
  fun e => by rw [ite_eq_left e] at h; cases h

/-- A sorted list of terms increases strictly in the order of terms. -/
public theorem sortedTerms_strictlyIncreasing {o : Orders} (hc : TotalCmp (Term.cmp o))
    (ts : List Term) : strictlyIncreasing (Term.cmp o) (sortedTerms o ts) = true := by
  have := hc.1; have := hc.2
  have h := (merge_spec (c := Term.cmp o) (fun _ _ => Std.LawfulEqCmp.eq_of_compare) id
    (fun _ => (0 : ℕ)) (fun a b => if a = b then some a else none) term_some term_none _
    (pairwise_sortBy (Term.cmp o) ts)).1
  rwa [List.map_id] at h

/-- The maximal elements increase strictly in the order of terms. -/
public theorem maxBases_strictlyIncreasing {o : Orders} (hc : TotalCmp (Term.cmp o))
    (bs : List Term) : strictlyIncreasing (Term.cmp o) (maxBases o bs) = true :=
  sortedTerms_strictlyIncreasing hc _

end Kalyx.Proofs.Terms
