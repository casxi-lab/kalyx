module

public import Kalyx.Statements.Terms
public import Kalyx.Proofs.Terms.Products

/-!
# The rounds of a product settle to one normal form

The confluence of the rounds of merging and reduction of a product
(`settleItems`), through a layered normal form that merges and reduces the
items of the largest depth first. It depends only on the coefficient, the
total of each key and the set of ones, and it does not change when one item
is reduced in place: for a root `ⁿ√u` by the floor carry
`⌊(a + s)/n⌋ = ⌊a/n⌋ + ⌊(a mod n + s)/n⌋` and the additivity of `u ^ q` in
`q`, for `i` by the group law of the signs. So `settleItems` returns the
normal form of its input, and settling a part of the items first changes
nothing but ones (`settleItems_regroup`, `settleItems_reduceItem`). Parts that
settle alike in every context (`SettleEq`) stay so when joined, folded or reduced
item by item, and their rounds return the same coefficient, and the same items where it
is not 0 (`SettleEq.settle`).
-/

namespace Kalyx.Proofs.Terms.Settle

open Kalyx.Spec.Terms Kalyx.Statements.Terms Kalyx.Proofs.Terms
open Kalyx.Proofs.Terms.Products (uItem uFactor itemParts_eq factorParts_eq forall₂_map depthList_le
  uFactor_depth Settled settleItems_succ reduceItem_cases exponentOf_eq_zero exponentOf_cons exponentOf_append
  exponentOf_flatMap)

/-! ## Reductions without the checks of exponents -/

/-- `reduceItem` without the checks of the exponents. -/
private def ured : Term × ℤ → ProductParts × List (Term × ℤ)
  | (b, k) =>
    if k = 0 then (ProductParts.unit, [])
    else if b = Term.imaginaryUnit then
      (⟨if k % 4 = 2 ∨ k % 4 = 3 then -1 else 1, if k % 4 = 1 ∨ k % 4 = 3 then [(b, 1)] else [],
        []⟩, [])
    else match rootOf b with
      | some (u, n) =>
        if (n : ℤ) ≤ k then
          (⟨(uFactor (k / n) u).coefficient, if k % n = 0 then [] else [(b, k % n)],
            (uFactor (k / n) u).ones⟩, (uFactor (k / n) u).items)
        else (⟨1, [(b, k)], []⟩, [])
      | none => (⟨1, [(b, k)], []⟩, [])

/-- The settled parts of the reduced items `M`, and the items they send back. -/
private def outs (M : List (Term × ℤ)) : ProductParts × List (Term × ℤ) :=
  (⟨(M.map fun x => (ured x).1.coefficient).prod, M.flatMap fun x => (ured x).1.items,
    M.flatMap fun x => (ured x).1.ones⟩, M.flatMap fun x => (ured x).2)

/-- The reductions of the items of a list, item by item. -/
@[simp] private theorem outs_cons (y : Term × ℤ) (M : List (Term × ℤ)) :
    outs (y :: M) = (⟨(ured y).1.coefficient * (outs M).1.coefficient,
      (ured y).1.items ++ (outs M).1.items, (ured y).1.ones ++ (outs M).1.ones⟩,
      (ured y).2 ++ (outs M).2) := by
  simp [outs]

/-- An item with the exponent 0 reduces to nothing. -/
private theorem ured_zero {x : Term × ℤ} (h : x.2 = 0) : ured x = (ProductParts.unit, []) := by
  obtain ⟨b, k⟩ := x; simp_all [ured]

/-- The merged items of `L` with an exponent other than 0. -/
private def layer (o : Orders) (L : List (Term × ℤ)) : List (Term × ℤ) :=
  (mergeItems o L).filter fun x => x.2 ≠ 0

/-- The items of the depth `d`. -/
private def top (d : ℕ) (L : List (Term × ℤ)) : List (Term × ℤ) :=
  L.filter fun x => decide (x.1.depth = d)

/-- The items of a depth other than `d`. -/
private def rest (d : ℕ) (L : List (Term × ℤ)) : List (Term × ℤ) :=
  L.filter fun x => !decide (x.1.depth = d)

/-- The parts below the layer `d` once its reduced items `r` settle into `p`. -/
private def below (d : ℕ) (r : ProductParts × List (Term × ℤ)) (p : ProductParts) : ProductParts :=
  ⟨p.coefficient * r.1.coefficient, rest d p.items ++ r.2, p.ones ++ r.1.ones⟩

/-- The layered normal form: the merged items of the depth `d + 1` reduce, and the
items they send back join the layers below; no items are left below the depth 1. -/
private def nf (o : Orders) : ℕ → ProductParts → ProductParts
  | 0, p => ⟨p.coefficient, [], p.ones⟩
  | d + 1, p =>
    let r := outs (layer o (top (d + 1) p.items))
    let q := nf o d (below (d + 1) r p)
    ⟨q.coefficient, r.1.items ++ q.items, q.ones⟩

/-- Parts with the same coefficient, the items up to order and the same ones as a set. -/
private def Equiv (p q : ProductParts) : Prop :=
  p.coefficient = q.coefficient ∧ p.items.Perm q.items ∧ ∀ b, b ∈ p.ones ↔ b ∈ q.ones

/-- Parts with the same coefficient, total exponent of each key and ones as a set. -/
private def Same (p q : ProductParts) : Prop :=
  p.coefficient = q.coefficient ∧ (∀ K, exponentOf K p.items = exponentOf K q.items) ∧
    ∀ b, b ∈ p.ones ↔ b ∈ q.ones

/-- `Equiv` is transitive. -/
private theorem Equiv.trans {p q r : ProductParts} (h : Equiv p q) (h' : Equiv q r) : Equiv p r :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, fun b => (h.2.2 b).trans (h'.2.2 b)⟩

/-! ## Total exponents -/

attribute [local simp] exponentOf_cons exponentOf_append exponentOf_flatMap

/-- The total exponent of a key over no items. -/
@[simp] private theorem exponentOf_nil (K : Key) : exponentOf K [] = 0 := rfl

/-- Total exponents do not depend on the order. -/
private theorem exponentOf_perm {L L' : List (Term × ℤ)} (h : L.Perm L') (K : Key) :
    exponentOf K L = exponentOf K L' := ((h.filter _).map _).sum_eq

/-- A filter constant on the items of a key keeps its total, or none of it. -/
private theorem exponentOf_filter (g : Term × ℤ → Bool) (K : Key) (s : Bool)
    (hg : ∀ x : Term × ℤ, Key.of x.1 x.2 = K → g x = s) (L : List (Term × ℤ)) :
    exponentOf K (L.filter g) = if s then exponentOf K L else 0 := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.filter_cons]
    by_cases hx : Key.of x.1 x.2 = K
    · have := hg x hx; split <;> simp_all
    · split <;> simp_all

/-- The items with the exponent 0 add nothing to the totals. -/
private theorem exponentOf_filter_ne (K : Key) (L : List (Term × ℤ)) :
    exponentOf K (L.filter fun x => x.2 ≠ 0) = exponentOf K L := by
  induction L with
  | nil => rfl
  | cons x L ih => rw [List.filter_cons]; split <;> simp_all

/-- A total of the nonnegative key of a base that is not a constant is nonnegative. -/
private theorem exponentOf_nonneg {b : Term} {k : ℤ} (hb : b.isConstant = false) (hk : 0 ≤ k)
    (L : List (Term × ℤ)) : 0 ≤ exponentOf (Key.of b k) L := by
  refine List.sum_nonneg fun e he => ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
  have h := of_decide_eq_true (List.mem_filter.1 hx).2; have e := congrArg Key.negative h
  rw [show x.1 = b from congrArg Key.base h] at e
  by_contra h'; simp [Key.of, hb, show ¬ k < 0 by omega, show x.2 < 0 by omega] at e

/-! ## Layers and their reduced items -/

variable {o : Orders}

/-- The merged items of a layer: their totals, other than 0. -/
private theorem mem_layer (hK : TotalCmp (Key.cmp o)) {L : List (Term × ℤ)} {x : Term × ℤ} :
    x ∈ layer o L ↔ x.2 = exponentOf (Key.of x.1 x.2) L ∧ x.2 ≠ 0 := by
  simp only [layer, List.mem_filter, mem_mergeItems hK, decide_eq_true_eq]
  exact ⟨fun ⟨⟨_, h⟩, h'⟩ => ⟨h, h'⟩, fun ⟨h, h'⟩ =>
    ⟨⟨by_contra fun hn => h' (h.trans (exponentOf_eq_zero hn)), h⟩, h'⟩⟩

/-- The keys of a layer increase strictly. -/
private theorem layer_strict (hK : TotalCmp (Key.cmp o)) (L : List (Term × ℤ)) :
    strictlyIncreasing (Key.cmp o) ((layer o L).map fun x => Key.of x.1 x.2) = true :=
  have := hK.1; strictlyIncreasing_filter_map (mergeItems_strictlyIncreasing hK L) _

/-- A layer depends only on the totals. -/
private theorem layer_congr (hK : TotalCmp (Key.cmp o)) {L L' : List (Term × ℤ)}
    (h : ∀ K, exponentOf K L = exponentOf K L') : layer o L = layer o L' :=
  have := hK.1
  eq_of_strictlyIncreasing_map _ (layer_strict hK L) (layer_strict hK L') fun x => by
    rw [mem_layer hK, mem_layer hK, h]

/-- A layer is, up to order, any list of distinct keys with its totals, without the exponents 0. -/
private theorem layer_perm (hK : TotalCmp (Key.cmp o)) {L N : List (Term × ℤ)}
    (hn : ((N.filter fun x => x.2 ≠ 0).map fun x => Key.of x.1 x.2).Nodup)
    (he : ∀ K, exponentOf K N = exponentOf K L) : (layer o L).Perm (N.filter fun x => x.2 ≠ 0) := by
  have hs := perm_sortBy (fun x y : Term × ℤ => Key.cmp o (Key.of x.1 x.2) (Key.of y.1 y.2))
    (N.filter fun x => x.2 ≠ 0)
  rw [layer_congr hK (L' := N.filter fun x => x.2 ≠ 0) fun K => by rw [exponentOf_filter_ne, he],
    layer, mergeItems_perm hK hs.symm, mergeItems_eq_self hK (strictlyIncreasing_sortBy_map hK _ hn),
    List.filter_eq_self.2 fun x hx => by simpa using (List.mem_filter.1 (hs.subset hx)).2]
  exact hs

/-- Reduced items that permute each other: the same settled parts and items sent back, up to order. -/
private def OutEq (M N : List (Term × ℤ)) : Prop :=
  (outs M).1.coefficient = (outs N).1.coefficient ∧ (outs M).1.items.Perm (outs N).1.items ∧
    (outs M).1.ones.Perm (outs N).1.ones ∧ (outs M).2.Perm (outs N).2

/-- Items with the exponent 0 reduce to nothing. -/
private theorem outs_filter (M : List (Term × ℤ)) : outs (M.filter fun x => x.2 ≠ 0) = outs M := by
  induction M with
  | nil => rfl
  | cons x M ih =>
    by_cases h : x.2 = 0
    · rw [List.filter_cons_of_neg (by simpa using h), ih, outs_cons, ured_zero h]; simp [ProductParts.unit]
    · rw [List.filter_cons_of_pos (by simpa using h), outs_cons, outs_cons, ih]

/-- The reduced items of a layer, against any list of distinct keys with the same totals. -/
private theorem outEq_layer (hK : TotalCmp (Key.cmp o)) {L N : List (Term × ℤ)}
    (hn : ((N.filter fun x => x.2 ≠ 0).map fun x => Key.of x.1 x.2).Nodup)
    (he : ∀ K, exponentOf K N = exponentOf K L) : OutEq (layer o L) N := by
  have hp := layer_perm hK hn he
  unfold OutEq; rw [← outs_filter N]
  exact ⟨(hp.map _).prod_eq, hp.flatMap_right _, hp.flatMap_right _, hp.flatMap_right _⟩

/-! ## The normal form depends only on the totals -/

/-- The totals of the items of one depth, and of the other depths. -/
private theorem exponentOf_top_rest (K : Key) (d : ℕ) (L : List (Term × ℤ)) :
    exponentOf K (top d L) = (if K.base.depth = d then exponentOf K L else 0) ∧
      exponentOf K (rest d L) = if K.base.depth = d then 0 else exponentOf K L := by
  rw [top, rest, exponentOf_filter (fun x => decide (x.1.depth = d)) K (decide (K.base.depth = d))
    (fun x hx => by rw [← hx]; rfl), exponentOf_filter (fun x => !decide (x.1.depth = d)) K
    (!decide (K.base.depth = d)) fun x hx => by rw [← hx]; rfl]; simp

/-- The normal forms of two parts whose layers below and reduced items correspond. -/
private theorem nf_succ {d : ℕ} {p q : ProductParts}
    (h : Equiv (nf o d (below (d + 1) (outs (layer o (top (d + 1) p.items))) p))
      (nf o d (below (d + 1) (outs (layer o (top (d + 1) q.items))) q)))
    (hi : (outs (layer o (top (d + 1) p.items))).1.items.Perm
      (outs (layer o (top (d + 1) q.items))).1.items) :
    Equiv (nf o (d + 1) p) (nf o (d + 1) q) := ⟨h.1, hi.append h.2.1, h.2.2⟩

/-- The normal form of parts with the same totals. -/
private theorem nf_congr (hK : TotalCmp (Key.cmp o)) :
    ∀ (D : ℕ) {p q : ProductParts}, Same p q → Equiv (nf o D p) (nf o D q)
  | 0, _, _, ⟨hc, _, ho⟩ => ⟨hc, .refl _, ho⟩
  | d + 1, p, q, ⟨hc, he, ho⟩ => by
    have hl : layer o (top (d + 1) p.items) = layer o (top (d + 1) q.items) :=
      layer_congr hK fun K => by rw [(exponentOf_top_rest K _ _).1, (exponentOf_top_rest K _ _).1, he]
    refine nf_succ (nf_congr hK d ⟨?_, fun K => ?_, fun b => ?_⟩) (by rw [hl])
    · simp only [below, hc, hl]
    · simp only [below, exponentOf_append, (exponentOf_top_rest K _ _).2, he, hl]
    · simp only [below, List.mem_append, ho, hl]

/-- The normal form of items in another order. -/
private theorem nf_perm (hK : TotalCmp (Key.cmp o)) (D : ℕ) {L L' : List (Term × ℤ)}
    (h : L.Perm L') : Equiv (nf o D ⟨1, L, []⟩) (nf o D ⟨1, L', []⟩) :=
  nf_congr hK D ⟨rfl, exponentOf_perm h, fun _ => Iff.rfl⟩

/-- The top layer and the rest of a list after items of another depth. -/
private theorem top_rest_ne {d : ℕ} {l : List (Term × ℤ)} (h : ∀ y ∈ l, y.1.depth ≠ d)
    (L : List (Term × ℤ)) : top d (l ++ L) = top d L ∧ rest d (l ++ L) = l ++ rest d L := by
  simp only [top, rest, List.filter_append]
  exact ⟨by rw [List.filter_eq_nil_iff.2 fun y hy => by simpa using h y hy]; rfl,
    by rw [List.filter_eq_self.2 fun y hy => by simpa using h y hy]⟩

/-- The top layer and the rest of a list after items of the depth. -/
private theorem top_rest_eq {d : ℕ} {l : List (Term × ℤ)} (h : ∀ y ∈ l, y.1.depth = d)
    (L : List (Term × ℤ)) : top d (l ++ L) = l ++ top d L ∧ rest d (l ++ L) = rest d L := by
  simp only [top, rest, List.filter_append]
  exact ⟨by rw [List.filter_eq_self.2 fun y hy => by simpa using h y hy],
    by rw [List.filter_eq_nil_iff.2 fun y hy => by simpa using h y hy]; rfl⟩

/-- Every term has a depth of at least 1. -/
private theorem depth_pos (t : Term) : 0 < t.depth := by
  cases t <;> simp [Term.depth]

/-- The radicand of a root is less deep than the root. -/
private theorem root_depth {b u : Term} {n : ℕ} (h : rootOf b = some (u, n)) : u.depth < b.depth := by
  obtain ⟨-, hd, rest, rfl, -⟩ := rootOf_some h
  simp only [Term.depth, Term.depthList]; omega

/-! ## Depths and reductions of single items -/

/-- An item has the exponent 0, is stable, is a power of `i`, or a power of a root that reduces. -/
private theorem item_cases (x : Term × ℤ) : x.2 = 0 ∨ Settled x ∨
    (x.1 = Term.imaginaryUnit ∧ x.2 ≠ 0) ∨
    (x.1 ≠ Term.imaginaryUnit ∧ ∃ u n, rootOf x.1 = some (u, n) ∧ (n : ℤ) ≤ x.2) := by
  by_cases h0 : x.2 = 0; · exact .inl h0
  by_cases hi : x.1 = Term.imaginaryUnit; · exact .inr (.inr (.inl ⟨hi, h0⟩))
  rcases hr : rootOf x.1 with _ | ⟨u, n⟩
  · exact .inr (.inl ⟨h0, fun h => absurd h hi, fun u n h => by rw [hr] at h; cases h⟩)
  by_cases hn : (n : ℤ) ≤ x.2
  · exact .inr (.inr (.inr ⟨hi, u, n, rfl, hn⟩))
  · exact .inr (.inl ⟨h0, fun h => absurd h hi, fun u' n' h => by rw [hr] at h; cases h; omega⟩)

/-- A stable item reduces to itself. -/
private theorem ured_stable {x : Term × ℤ} (h : Settled x) : ured x = (⟨1, [x], []⟩, []) := by
  obtain ⟨b, k⟩ := x
  obtain ⟨h0, hi, hr⟩ := h
  by_cases hb : b = Term.imaginaryUnit
  · subst hb; obtain rfl := hi rfl; simp [ured]
  rcases e : rootOf b with _ | ⟨u, n⟩
  · simp [ured, h0, hb, e]
  · simp [ured, h0, hb, e, not_le.2 (hr u n e)]

/-- The powers of `i`. -/
private theorem ured_i (m : ℤ) : ured (Term.imaginaryUnit, m) =
    (⟨if m % 4 = 2 ∨ m % 4 = 3 then -1 else 1,
      if m % 4 = 1 ∨ m % 4 = 3 then [(Term.imaginaryUnit, 1)] else [], []⟩, []) := by
  by_cases hm : m = 0
  · subst hm; rfl
  · simp [ured, hm]

/-- The powers of a root. -/
private theorem ured_root {b u : Term} {n : ℕ} (hb : b ≠ Term.imaginaryUnit)
    (hr : rootOf b = some (u, n)) (m : ℤ) : ured (b, m) =
      if (n : ℤ) ≤ m then (⟨(uFactor (m / n) u).coefficient, if m % n = 0 then [] else [(b, m % n)],
        (uFactor (m / n) u).ones⟩, (uFactor (m / n) u).items)
      else (⟨1, if m = 0 then [] else [(b, m)], []⟩, []) := by
  have := (rootOf_some hr).1
  by_cases hm : m = 0
  · subst hm; rw [ite_eq_right (by omega)]; rfl
  · simp [ured, hm, hb, hr]

/-- The items of a reduction: at most one, on the base and of the key of the item, stable. -/
private theorem ured_items (x : Term × ℤ) : (ured x).1.items = [] ∨ ∃ k',
    (ured x).1.items = [(x.1, k')] ∧ Key.of x.1 k' = Key.of x.1 x.2 ∧ Settled (x.1, k') := by
  rcases item_cases x with h | h | ⟨hb, h0⟩ | ⟨hb, u, n, hr, hn⟩
  · rw [ured_zero h]; exact .inl rfl
  · rw [ured_stable h]; exact .inr ⟨x.2, rfl, rfl, h⟩
  · obtain ⟨b, k⟩ := x; simp only at hb; subst hb
    by_cases h : k % 4 = 1 ∨ k % 4 = 3
    · exact .inr ⟨1, by simp [ured_i, h], by simp [Key.of, Term.imaginaryUnit, Term.isConstant],
        by simp [Settled, rootOf, Term.imaginaryUnit]⟩
    · exact .inl (by simp [ured_i, h])
  · obtain ⟨b, k⟩ := x; simp only at hb hr hn
    have := (rootOf_some hr).1
    rw [ured_root hb hr, ite_eq_left hn]; split
    · exact .inl rfl
    · have := Int.emod_nonneg k (show (n : ℤ) ≠ 0 by omega)
      have := Int.emod_lt_of_pos k (show (0 : ℤ) < n by omega)
      refine .inr ⟨k % n, rfl, by simp [Key.of, show ¬ k % n < 0 by omega, show ¬ k < 0 by omega],
        ⟨‹_›, fun h => absurd h hb, ?_⟩⟩
      intro u' n' e; rw [hr] at e; cases e; omega

/-- The items that a reduction sends back are less deep than the item. -/
private theorem ured_back (x : Term × ℤ) : ∀ y ∈ (ured x).2, y.1.depth < x.1.depth := by
  rcases item_cases x with h | h | ⟨hb, h0⟩ | ⟨hb, u, n, hr, hn⟩
  · simp [ured_zero h]
  · simp [ured_stable h]
  · obtain ⟨b, k⟩ := x; simp only at hb; subst hb; simp [ured_i]
  · obtain ⟨b, k⟩ := x; simp only at hb hr hn
    rw [ured_root hb hr, ite_eq_left hn]; have := (rootOf_some hr).1
    exact fun y hy => (uFactor_depth (ne_of_gt (Int.le_ediv_of_mul_le (by omega) (by omega) :
      (0 : ℤ) < k / n)) u y hy).1.trans_lt (root_depth hr)

/-- The items of a reduction are no deeper than the item. -/
private theorem ured_depth (x : Term × ℤ) :
    ∀ y ∈ (ured x).1.items ++ (ured x).2, y.1.depth ≤ x.1.depth := by
  intro y hy; rcases List.mem_append.1 hy with hy | hy
  · rcases ured_items x with e | ⟨k'', e, -⟩ <;> rw [e] at hy
    · simp at hy
    · rw [List.mem_singleton.1 hy]
  · exact (ured_back x y hy).le

/-- A positive multiple of an exponent has its key. -/
private theorem key_mul (t : Term) (j : ℤ) {q : ℤ} (hq : 0 < q) : Key.of t (j * q) = Key.of t j := by
  have : j * q < 0 ↔ j < 0 := ⟨fun h => by nlinarith, fun h => by nlinarith⟩
  simp [Key.of, this]

/-- The total of one item is additive in nonnegative multiples of its exponent. -/
private theorem exp_single (t : Term) (j : ℤ) {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (K : Key) :
    exponentOf K [(t, j * (a + b))] = exponentOf K [(t, j * a)] + exponentOf K [(t, j * b)] := by
  rcases ha.eq_or_lt with rfl | ha; · simp
  rcases hb.eq_or_lt with rfl | hb; · simp
  simp only [exponentOf_cons, exponentOf_nil, add_zero, key_mul t j ha, key_mul t j hb,
    key_mul t j (add_pos ha hb)]
  split <;> ring

/-- The coefficient of a power of a factor is multiplicative in the exponent. -/
private theorem uItem_coef {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (f : Term) :
    (uItem (a + b) f).coefficient = (uItem a f).coefficient * (uItem b f).coefficient := by
  cases f with
  | sum c ms => exact zpow_add' (.inr (by omega))
  | power c j => by_cases hj : j = 0 <;> simp [uItem, hj]
  | _ => exact (mul_one 1).symm

/-- The totals of a power of a factor are additive in the exponent. -/
private theorem uItem_exp {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (K : Key) (f : Term) :
    exponentOf K (uItem (a + b) f).items =
      exponentOf K (uItem a f).items + exponentOf K (uItem b f).items := by
  cases f with
  | power c j =>
    by_cases hj : j = 0
    · simp [uItem, hj]
    · simpa [uItem, hj] using exp_single c j ha hb K
  | _ => simpa [uItem] using exp_single _ 1 ha hb K

/-- The coefficient and the totals of a power of a term are additive in the exponent. -/
private theorem uFactor_add (u : Term) {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (uFactor (a + b) u).coefficient = (uFactor a u).coefficient * (uFactor b u).coefficient ∧
      ∀ K, exponentOf K (uFactor (a + b) u).items =
        exponentOf K (uFactor a u).items + exponentOf K (uFactor b u).items := by
  have hz : ∀ r : ℚ, r ^ (a + b) = r ^ a * r ^ b := fun r => zpow_add' (.inr (by omega))
  cases u with
  | number r => exact ⟨hz r, fun K => by simp [uFactor]⟩
  | product c fs =>
    simp only [uFactor, foldl_append, List.map_map, Function.comp_def, List.nil_append,
      ← List.flatMap_def, exponentOf_flatMap, uItem_coef ha hb, uItem_exp ha hb, List.prod_map_mul,
      List.sum_map_add, hz]
    exact ⟨by ring, fun _ => trivial⟩
  | _ => exact ⟨uItem_coef ha hb _, fun K => uItem_exp ha hb K _⟩

/-- The ones of a power of a factor do not depend on the exponent. -/
private theorem uItem_ones (q q' : ℤ) (f : Term) : (uItem q f).ones = (uItem q' f).ones := by
  cases f with
  | power c j => by_cases hj : j = 0 <;> simp [uItem, hj]
  | _ => rfl

/-- The ones of a power of a term do not depend on the exponent. -/
private theorem uFactor_ones (q q' : ℤ) (u : Term) : (uFactor q u).ones = (uFactor q' u).ones := by
  cases u with
  | number => rfl
  | product c fs => simp only [uFactor, foldl_append, List.map_map, Function.comp_def, uItem_ones q q']
  | _ => exact uItem_ones q q' _

/-! ## One item reduced in place -/

/-- The reduction of an item `x` that leaves the exponent `k'` on its base (none
for 0) commutes with merging: for every total `T` of the other items of its key,
reducing `x.2 + T` at once gives what reducing `x` and then `k' + T` gives. -/
private def Compat (x : Term × ℤ) (k' : ℤ) : Prop :=
  (ured x).1.items = (if k' = 0 then [] else [(x.1, k')]) ∧
    (k' ≠ 0 → Key.of x.1 k' = Key.of x.1 x.2) ∧
    ∀ T : ℤ, (x.1.isConstant = false → 0 ≤ x.2 → 0 ≤ T) →
      (ured (x.1, x.2 + T)).1.coefficient =
          (ured x).1.coefficient * (ured (x.1, k' + T)).1.coefficient ∧
        (ured (x.1, x.2 + T)).1.items = (ured (x.1, k' + T)).1.items ∧
        (∀ z, z ∈ (ured (x.1, x.2 + T)).1.ones ↔
          z ∈ (ured x).1.ones ∨ z ∈ (ured (x.1, k' + T)).1.ones) ∧
        ∀ K, exponentOf K (ured (x.1, x.2 + T)).2 =
          exponentOf K (ured x).2 + exponentOf K (ured (x.1, k' + T)).2

/-- The powers of `i` commute with merging: the group law of the signs. -/
private theorem compat_i (k : ℤ) : Compat (Term.imaginaryUnit, k) (k % 2) := by
  refine ⟨?_, fun _ => by simp [Key.of, Term.imaginaryUnit, Term.isConstant], fun T _ => ?_⟩
  · simp only [ured_i]; split_ifs <;> first | rfl | omega | (simp; omega)
  · simp only [ured_i]
    refine ⟨?_, ?_, by simp, by simp⟩
    · split_ifs <;> first | omega | norm_num
    · split_ifs <;> first | rfl | omega

/-- The powers of a root commute with merging: the floor carry. -/
private theorem compat_root {b u : Term} {n : ℕ} {k : ℤ} (hb : b ≠ Term.imaginaryUnit)
    (hr : rootOf b = some (u, n)) (hn : (n : ℤ) ≤ k) : Compat (b, k) (k % n) := by
  have hc : b.isConstant = false := by obtain ⟨-, hd, rest, rfl, -⟩ := rootOf_some hr; rfl
  have hn0 : (0 : ℤ) < n := by have := (rootOf_some hr).1; omega
  have hm := Int.emod_nonneg k hn0.ne'; have hm' := Int.emod_lt_of_pos k hn0
  refine ⟨by simp only [ured_root hb hr, ite_eq_left hn], fun _ => by
    simp [Key.of, show ¬ k % n < 0 by omega, show ¬ k < 0 by omega], fun T hT => ?_⟩
  have hT := hT hc (by omega)
  have e0 : k + T = k % n + T + n * (k / n) := by linarith [Int.emod_add_mul_ediv k n]
  have e1 : (k + T) / n = k / n + (k % n + T) / n := by
    rw [e0, Int.add_mul_ediv_left _ _ hn0.ne']; ring
  have e2 : (k + T) % n = (k % n + T) % n := by rw [e0, Int.add_mul_emod_self_left]
  have hq : 0 ≤ k / n := Int.ediv_nonneg (by omega) hn0.le
  simp only [ured_root hb hr, ite_eq_left hn, ite_eq_left (show (n : ℤ) ≤ k + T by omega), e1, e2]
  by_cases h : (n : ℤ) ≤ k % n + T
  · obtain ⟨c1, c2⟩ := uFactor_add u (b := (k % n + T) / n) hq (Int.ediv_nonneg (by omega) hn0.le)
    simp only [ite_eq_left h]
    refine ⟨c1, by simp, fun z => ?_, c2⟩
    rw [uFactor_ones (k / n + (k % n + T) / n) 0, uFactor_ones (k / n) 0,
      uFactor_ones ((k % n + T) / n) 0, or_self]
  · have e3 : (k % n + T) / n = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
    have e4 : (k % n + T) % n = k % n + T := Int.emod_eq_of_lt (by omega) (by omega)
    simp [ite_eq_right h, e3, e4]

/-- The reduced items of a layer of `L'`, split at a key `K` on the base `b`: its
total, and the other keys of a layer of `L₀` that has their totals. -/
private theorem outEq_split (hK : TotalCmp (Key.cmp o)) {L' L₀ : List (Term × ℤ)} {K : Key}
    {b : Term} (hb : K.base = b) (h : ∀ K', K' ≠ K → exponentOf K' L' = exponentOf K' L₀) :
    OutEq (layer o L') ((b, exponentOf K L') :: (layer o L₀).filter fun y => Key.of y.1 y.2 ≠ K) := by
  subst hb
  have ht : exponentOf K L' ≠ 0 → Key.of K.base (exponentOf K L') = K := fun h =>
    key_exponentOf hK (by_contra fun hn => h (exponentOf_eq_zero hn))
  have hs : (((layer o L₀).filter fun y => Key.of y.1 y.2 ≠ K).filter fun y => y.2 ≠ 0).Sublist
      (layer o L₀) := List.filter_sublist.trans List.filter_sublist
  have := hK.1
  have hn := (nodup_of_pairwise_lt (strictlyIncreasing_iff_pairwise.1 (layer_strict hK L₀))).sublist
    (hs.map fun y => Key.of y.1 y.2)
  refine outEq_layer hK ?_ fun K' => ?_
  · rw [List.filter_cons]; split
    · refine List.nodup_cons.2 ⟨fun hm => ?_, hn⟩
      obtain ⟨y, hy, e⟩ := List.mem_map.1 hm
      have := (List.mem_filter.1 (List.mem_filter.1 hy).1).2
      simp_all
    · exact hn
  rw [exponentOf_cons, exponentOf_filter _ K' (decide (K' ≠ K)) (fun y hy => by rw [hy]),
    layer, exponentOf_filter_ne, exponentOf_mergeItems hK]
  by_cases e : K' = K
  · subst e; by_cases h0 : exponentOf K' L' = 0 <;> simp [h0, ht]
  · by_cases h0 : exponentOf K L' = 0 <;> simp [e, h0, ht, Ne.symm e, h K' e]

/-- One item of the top layer reduced in place, given that its reduction commutes
with merging. -/
private theorem reduce_top (hK : TotalCmp (Key.cmp o)) {x : Term × ℤ} {k' : ℤ}
    (hx : Compat x k') {d : ℕ} (hd : x.1.depth = d + 1) (c : ℚ) (L : List (Term × ℤ))
    (ones : List Term) :
    Equiv (nf o (d + 1) ⟨c, x :: L, ones⟩) (nf o (d + 1)
      ⟨c * (ured x).1.coefficient, (ured x).1.items ++ (ured x).2 ++ L, ones ++ (ured x).1.ones⟩) := by
  obtain ⟨hi, hk', hC⟩ := hx
  set T := exponentOf (Key.of x.1 x.2) (top (d + 1) L) with hT
  obtain ⟨C1, C2, C3, C4⟩ := hC T fun hb h0 => exponentOf_nonneg hb h0 _
  have hb : ∀ y ∈ (ured x).2, y.1.depth ≤ d := fun y hy => by have := ured_back x y hy; omega
  have hI : ∀ y ∈ (ured x).1.items, y.1 = x.1 := by rw [hi]; split <;> simp
  obtain ⟨ht1, hr1⟩ := top_rest_eq (l := [x]) (by simpa using hd) L
  obtain ⟨ht2, hr2⟩ := top_rest_eq (fun y hy => (hI y hy) ▸ hd) ((ured x).2 ++ L)
  obtain ⟨ht3, hr3⟩ := top_rest_ne (d := d + 1) (fun y hy => by have := hb y hy; omega) L
  simp only [List.singleton_append] at ht1 hr1
  have o1 := outEq_split hK (L' := x :: top (d + 1) L) (L₀ := top (d + 1) L)
    (K := Key.of x.1 x.2) (b := x.1) rfl fun K' h => by simp [Ne.symm h]
  have o2 := outEq_split hK (L' := (ured x).1.items ++ top (d + 1) L) (L₀ := top (d + 1) L)
    (K := Key.of x.1 x.2) (b := x.1) rfl fun K' h => by
      rw [exponentOf_append, hi]; split
      · simp
      · simp [hk' ‹_›, Ne.symm h]
  rw [show exponentOf (Key.of x.1 x.2) (x :: top (d + 1) L) = x.2 + T by simp [hT]] at o1
  rw [show exponentOf (Key.of x.1 x.2) ((ured x).1.items ++ top (d + 1) L) = k' + T by
    rw [exponentOf_append, hi]; split <;> simp [*]] at o2
  refine nf_succ (nf_congr hK d ⟨?_, fun K' => ?_, fun z => ?_⟩) ?_ <;>
    simp only [below, List.append_assoc, ht1, ht2, ht3, hr1, hr2, hr3]
  · rw [o1.1, o2.1]; simp only [outs_cons, C1]; ring
  · rw [exponentOf_append, exponentOf_append, exponentOf_append, exponentOf_perm o1.2.2.2,
      exponentOf_perm o2.2.2.2]
    simp only [outs_cons, exponentOf_append, C4]; ring
  · simp only [List.mem_append, o1.2.2.1.mem_iff, o2.2.2.1.mem_iff, outs_cons, C3]; tauto
  · refine o1.2.1.trans (List.Perm.trans ?_ o2.2.1.symm); simp only [outs_cons, C2]; exact .refl _

/-- One item reduced in place, given that its reduction commutes with merging. -/
private theorem reduce_one (hK : TotalCmp (Key.cmp o)) {x : Term × ℤ} {k' : ℤ} (hx : Compat x k') :
    ∀ (D : ℕ) (c : ℚ) (L : List (Term × ℤ)) (ones : List Term), x.1.depth ≤ D →
      Equiv (nf o D ⟨c, x :: L, ones⟩) (nf o D
        ⟨c * (ured x).1.coefficient, (ured x).1.items ++ (ured x).2 ++ L, ones ++ (ured x).1.ones⟩)
  | 0, _, _, _, h => absurd h (by have := depth_pos x.1; omega)
  | d + 1, c, L, ones, h => by
    rcases (show x.1.depth = d + 1 ∨ x.1.depth ≤ d by omega) with h' | h'
    · exact reduce_top hK hx h' c L ones
    obtain ⟨ht, hr⟩ := top_rest_ne (d := d + 1) (fun y hy => by have := ured_depth x y hy; omega) L
    obtain ⟨ht', hr'⟩ := top_rest_ne (l := [x]) (by simpa using (by omega : x.1.depth ≠ d + 1)) L
    simp only [List.singleton_append] at ht' hr'
    refine nf_succ ?_ (by simp only [ht, ht']; exact .refl _)
    simp only [below, ht, ht', hr, hr', List.cons_append]
    exact (reduce_one hK hx d _ _ _ h').trans
      (nf_congr hK d ⟨by ring, fun K => by simp, fun z => by simp; tauto⟩)

/-- One item reduced in place. -/
private theorem reduce_any (hK : TotalCmp (Key.cmp o)) (x : Term × ℤ) (D : ℕ) (c : ℚ)
    (L : List (Term × ℤ)) (ones : List Term) (h : x.1.depth ≤ D) :
    Equiv (nf o D ⟨c, x :: L, ones⟩) (nf o D
      ⟨c * (ured x).1.coefficient, (ured x).1.items ++ (ured x).2 ++ L, ones ++ (ured x).1.ones⟩) := by
  rcases item_cases x with h0 | hs | ⟨hb, h0⟩ | ⟨hb, u, n, hr, hn⟩
  · rw [ured_zero h0]
    exact nf_congr hK D ⟨by simp [ProductParts.unit], fun K => by simp [ProductParts.unit, h0],
      fun z => by simp [ProductParts.unit]⟩
  · rw [ured_stable hs]; exact nf_congr hK D ⟨by simp, fun K => by simp, fun z => by simp⟩
  · obtain ⟨b, k⟩ := x; simp only at hb h0; subst hb
    exact reduce_one hK (compat_i k) D c L ones h
  · obtain ⟨b, k⟩ := x; exact reduce_one hK (compat_root hb hr hn) D c L ones h

/-- The items of a list reduced in place, one after the other. -/
private theorem reduce_list (hK : TotalCmp (Key.cmp o)) (D : ℕ) :
    ∀ (M : List (Term × ℤ)) (c : ℚ) (L : List (Term × ℤ)) (ones : List Term),
      (∀ x ∈ M, x.1.depth ≤ D) → Equiv (nf o D ⟨c, M ++ L, ones⟩) (nf o D
        ⟨c * (outs M).1.coefficient, (outs M).1.items ++ (outs M).2 ++ L, ones ++ (outs M).1.ones⟩)
  | [], c, L, ones, _ => nf_congr hK D ⟨by simp [outs], fun K => by simp [outs], fun z => by simp [outs]⟩
  | x :: M, c, L, ones, h => by
    refine (reduce_any hK x D c (M ++ L) ones (h x (by simp))).trans ?_
    refine (nf_congr hK D (q := ⟨c * (ured x).1.coefficient, M ++ ((ured x).1.items ++ (ured x).2 ++ L),
      ones ++ (ured x).1.ones⟩) (by
        refine ⟨rfl, fun K => ?_, fun z => Iff.rfl⟩; simp only [exponentOf_append]; ring)).trans ?_
    refine (reduce_list hK D M _ _ _ fun y hy => h y (by simp [hy])).trans
      (nf_congr hK D ⟨?_, fun K => ?_, fun z => ?_⟩)
    · simp only [outs_cons]; ring
    · simp only [outs_cons, exponentOf_append]; ring
    · simp only [outs_cons, List.mem_append]; tauto

/-- The reduced items of stable items are those items. -/
private theorem outs_stable : ∀ {M : List (Term × ℤ)}, (∀ x ∈ M, Settled x) →
    outs M = (⟨1, M, []⟩, [])
  | [], _ => rfl
  | x :: M, h => by
    rw [outs_cons, ured_stable (h x (by simp)), outs_stable fun y hy => h y (by simp [hy])]; simp

/-- The items of reduced items are stable, on the bases of the items. -/
private theorem mem_outs {M : List (Term × ℤ)} {y : Term × ℤ} (h : y ∈ (outs M).1.items) :
    Settled y ∧ ∃ x ∈ M, y.1 = x.1 := by
  simp only [outs, List.mem_flatMap] at h
  obtain ⟨x, hx, hy⟩ := h
  rcases ured_items x with e | ⟨k', e, -, hs⟩ <;> rw [e] at hy
  · simp at hy
  · rw [List.mem_singleton.1 hy]; exact ⟨hs, x, hx, rfl⟩

/-- The keys of reduced items are among the keys of the items, in their order. -/
private theorem outs_keys : ∀ M : List (Term × ℤ),
    ((outs M).1.items.map fun y => Key.of y.1 y.2).Sublist (M.map fun y => Key.of y.1 y.2)
  | [] => by simp [outs]
  | x :: M => by
    simp only [outs_cons, List.map_append, List.map_cons]
    rcases ured_items x with e | ⟨k', e, hk, -⟩ <;> rw [e]
    · exact (outs_keys M).cons (Key.of x.1 x.2)
    · simpa [hk] using (outs_keys M).cons_cons (Key.of x.1 x.2)

/-- The items of a round are no deeper than the items it starts from. -/
private theorem outs_depth {M : List (Term × ℤ)} {D : ℕ} (h : ∀ x ∈ M, x.1.depth ≤ D) :
    ∀ y ∈ (outs M).1.items ++ (outs M).2, y.1.depth ≤ D := by
  intro y hy
  simp only [outs, List.mem_append, List.mem_flatMap] at hy
  rcases hy with ⟨x, hx, hy⟩ | ⟨x, hx, hy⟩
  exacts [(ured_depth x y (List.mem_append_left _ hy)).trans (h x hx),
    (ured_depth x y (List.mem_append_right _ hy)).trans (h x hx)]

/-- A merged item has the base of an item. -/
private theorem mergeItems_depth (hK : TotalCmp (Key.cmp o)) {L : List (Term × ℤ)} {D : ℕ}
    (h : ∀ x ∈ L, x.1.depth ≤ D) : ∀ x ∈ mergeItems o L, x.1.depth ≤ D := fun x hx => by
  obtain ⟨y, hy, e⟩ := List.mem_map.1 ((mem_mergeItems hK).1 hx).1
  have e' : y.1 = x.1 := congrArg Key.base e
  rw [← e']; exact h y hy

/-- Settled items of distinct keys are their own normal form. -/
private theorem stable_nf (hK : TotalCmp (Key.cmp o)) : ∀ (D : ℕ) (p : ProductParts),
    (∀ x ∈ p.items, Settled x ∧ x.1.depth ≤ D) → (p.items.map fun x => Key.of x.1 x.2).Nodup →
      Equiv (nf o D p) p
  | 0, p, h, _ => ⟨rfl, by
      rw [List.eq_nil_iff_forall_not_mem.2 fun x hx => absurd (h x hx).2 (by
        have := depth_pos x.1; omega)]; exact .nil, fun _ => Iff.rfl⟩
  | d + 1, p, h, hn => by
    have hs : (top (d + 1) p.items).Sublist p.items := List.filter_sublist
    have hst : ∀ x ∈ top (d + 1) p.items, Settled x := fun x hx => (h x (hs.subset hx)).1
    have hf : (top (d + 1) p.items).filter (fun x => x.2 ≠ 0) = top (d + 1) p.items :=
      List.filter_eq_self.2 fun x hx => by simpa using (hst x hx).1
    have e := outEq_layer hK (L := top (d + 1) p.items) (N := top (d + 1) p.items)
      (by rw [hf]; exact hn.sublist (hs.map _)) fun _ => rfl
    unfold OutEq at e; rw [outs_stable hst] at e
    obtain ⟨h1, h2, h3⟩ := (nf_congr hK d (p := below (d + 1) (outs (layer o (top (d + 1) p.items))) p)
      (q := ⟨p.coefficient, rest (d + 1) p.items, p.ones⟩) (by
      refine ⟨?_, fun K => ?_, fun z => ?_⟩ <;>
        simp [below, e.1, exponentOf_perm e.2.2.2, e.2.2.1.mem_iff])).trans
      (stable_nf hK d _ (fun x hx => ⟨(h x (List.filter_sublist.subset hx)).1, by
        have := (h x (List.filter_sublist.subset hx)).2; have := (List.mem_filter.1 hx).2
        simp at this; omega⟩) (hn.sublist (List.filter_sublist.map _)))
    exact ⟨h1, (e.2.1.append h2).trans (List.filter_append_perm _ _), h3⟩

/-! ## The rounds compute the normal form: stable items, keys and depths -/

/-- A checked reduction is the reduction without the checks. -/
private theorem reduceItem_value {me : ℕ} {x : Term × ℤ} {r : ProductParts × List (Term × ℤ)}
    (h : reduceItem me x = .value r) : r = ured x := by
  obtain ⟨b, k⟩ := x
  rcases reduceItem_cases h with ⟨rfl, rfl⟩ | ⟨hk, hb, rfl⟩ | ⟨hk, hb, u, n, hr, hn, rfl⟩ |
    ⟨hk, hb, hr, rfl⟩
  · rfl
  all_goals rcases e : rootOf b with _ | ⟨u', n'⟩ <;> simp_all [ured]

/-- A round of `settleItems` that returns a value: the last round, or the next rounds. -/
private theorem settle_succ {me f : ℕ} {p p' : ProductParts} {r : ProductParts × List (Term × ℤ)}
    (h : settleItems o me (f + 1) p = .value p') (hr : outs (mergeItems o p.items) = r) :
    (r.2 = [] ∧ p' = ⟨p.coefficient * r.1.coefficient, r.1.items, p.ones ++ r.1.ones⟩) ∨
      settleItems o me f ⟨p.coefficient * r.1.coefficient, r.1.items ++ r.2, p.ones ++ r.1.ones⟩ =
        .value p' := by
  subst hr; rw [settleItems_succ] at h
  obtain ⟨rs, hrs, h⟩ := bind_eq_value.1 h
  rw [forall₂_map (mapM_value hrs) fun _ _ _ => reduceItem_value] at h
  split at h
  · rename_i hc; cases h
    exact .inl ⟨by simpa [outs, List.flatMap_def, Function.comp_def] using List.isEmpty_iff.1 hc,
      by simp [outs, List.flatMap_def, Function.comp_def]⟩
  · exact .inr (by simpa [outs, List.flatMap_def, Function.comp_def] using h)

/-- The items the rounds return: stable, no deeper than at the start, of increasing keys. -/
private theorem settle_out (hK : TotalCmp (Key.cmp o)) {me D : ℕ} : ∀ (f : ℕ) {p p' : ProductParts},
    settleItems o me f p = .value p' → (∀ x ∈ p.items, x.1.depth ≤ D) →
    (∀ x ∈ p'.items, Settled x ∧ x.1.depth ≤ D) ∧
      (p'.items.map fun x => Key.of x.1 x.2).Pairwise fun a b => Key.cmp o a b = .lt
  | 0, _, _, h, _ => by simp [settleItems] at h
  | f + 1, p, p', h, hD => by
    have hM := mergeItems_depth hK hD
    rcases settle_succ h rfl with ⟨-, rfl⟩ | h'
    · have := hK.1
      exact ⟨fun y hy => ⟨(mem_outs hy).1, outs_depth hM y (List.mem_append_left _ hy)⟩,
        (strictlyIncreasing_iff_pairwise.1 (mergeItems_strictlyIncreasing hK _)).sublist
          (outs_keys _)⟩
    · exact settle_out hK f h' (outs_depth hM)

/-- Settling a part of the items first keeps the normal form, in any context. -/
private theorem ctx (hK : TotalCmp (Key.cmp o)) {me D : ℕ} : ∀ (f : ℕ) {b b' : ProductParts},
    settleItems o me f b = .value b' → ∀ (c : ℚ) (L : List (Term × ℤ)) (ones : List Term),
    (∀ x ∈ L ++ b.items, x.1.depth ≤ D) →
    Equiv (nf o D ⟨c * b.coefficient, L ++ b.items, ones ++ b.ones⟩)
      (nf o D ⟨c * b'.coefficient, L ++ b'.items, ones ++ b'.ones⟩)
  | 0, _, _, h => by simp [settleItems] at h
  | f + 1, b, b', h => fun c L ones hD => by
    have hM := mergeItems_depth hK fun x hx => hD x (List.mem_append_right _ hx)
    have e1 := (nf_congr hK D (p := ⟨c * b.coefficient, L ++ b.items, ones ++ b.ones⟩)
      (q := ⟨c * b.coefficient, mergeItems o b.items ++ L, ones ++ b.ones⟩)
      (by refine ⟨rfl, fun K => ?_, fun _ => Iff.rfl⟩
          rw [exponentOf_append, exponentOf_append, exponentOf_mergeItems hK]; ring)).trans
      (reduce_list hK D _ _ L _ hM)
    have e2 := e1.trans (nf_congr hK D (q := ⟨c * (b.coefficient * (outs (mergeItems o b.items)).1.coefficient),
      L ++ ((outs (mergeItems o b.items)).1.items ++ (outs (mergeItems o b.items)).2),
      ones ++ (b.ones ++ (outs (mergeItems o b.items)).1.ones)⟩) (by
        refine ⟨by ring, fun K => ?_, fun z => ?_⟩
        · simp only [exponentOf_append]; ring
        · simp only [List.mem_append]; tauto))
    rcases settle_succ h rfl with ⟨hb, rfl⟩ | h'
    · rwa [hb, List.append_nil] at e2
    · exact e2.trans (ctx hK f h' c L ones fun x hx => by
        rcases List.mem_append.1 hx with hx | hx
        exacts [hD x (List.mem_append_left _ hx), outs_depth hM x hx])

/-- The parts that `settleItems` returns are the normal form of its input. -/
private theorem settle_nf (hK : TotalCmp (Key.cmp o)) {me f D : ℕ} {p p' : ProductParts}
    (h : settleItems o me f p = .value p') (hD : ∀ x ∈ p.items, x.1.depth ≤ D) :
    Equiv (nf o D p) p' := by
  have ho := settle_out hK f h hD
  have := hK.1
  refine (nf_congr hK D ⟨?_, fun K => ?_, fun z => ?_⟩).trans ((ctx hK f h 1 [] [] (by simpa using hD)).trans
    ((nf_congr hK D ⟨?_, fun K => ?_, fun z => ?_⟩).trans
      (stable_nf hK D p' ho.1 (nodup_of_pairwise_lt ho.2))))
  all_goals simp

/-- The normal form scales with the coefficient and keeps the ones. -/
private theorem nf_scale (D : ℕ) : ∀ (c : ℚ) (L : List (Term × ℤ)) (ones : List Term),
    nf o D ⟨c, L, ones⟩ = ⟨c * (nf o D ⟨1, L, []⟩).coefficient, (nf o D ⟨1, L, []⟩).items,
      ones ++ (nf o D ⟨1, L, []⟩).ones⟩ := by
  induction D with
  | zero => intro c L ones; simp [nf]
  | succ d ih =>
    intro c L ones
    simp only [nf, below]
    rw [ih (c * _) _ (ones ++ _), ih (1 * _) _ ([] ++ _)]
    simp [mul_assoc]

/-! ## The confluence of the rounds -/

/-- A bound on the depths of the bases of items. -/
private theorem depth_bound (L : List (Term × ℤ)) :
    ∀ x ∈ L, x.1.depth ≤ Term.depthList (L.map Prod.fst) :=
  fun _ hx => depthList_le.1 le_rfl _ (List.mem_map_of_mem hx)

/-- The items that `settleItems` returns are stable: an exponent other than 0,
`i` only with the exponent 1, and a root of the degree `n` only with an
exponent below `n`; and their keys increase strictly. -/
public theorem settleItems_items {o : Orders} (hK : TotalCmp (Key.cmp o)) {me f : ℕ}
    {p p' : ProductParts} (h : settleItems o me f p = .value p') :
    (∀ x ∈ p'.items, x.2 ≠ 0 ∧ (x.1 = Term.imaginaryUnit → x.2 = 1) ∧
      ∀ u n, rootOf x.1 = some (u, n) → x.2 < n) ∧
      strictlyIncreasing (Key.cmp o) (p'.items.map fun x => Key.of x.1 x.2) = true :=
  have := hK.1
  have ho := settle_out hK f h (depth_bound p.items)
  ⟨fun x hx => (ho.1 x hx).1, strictlyIncreasing_iff_pairwise.2 ho.2⟩

/-- Settling a part `b` first: the rounds of `items₀` with the items of `b` give
the coefficient and the ones of a part `q` scaled by that of `b'` and joined with
`ones₁` and those of `b'`; those of `items₀` with the items of `b'`, the same items. -/
public theorem settleItems_regroup {o : Orders} (hK : TotalCmp (Key.cmp o)) {me f₁ f₂ : ℕ}
    {b b' p : ProductParts} {c : ℚ} {items₀ items₁ : List (Term × ℤ)} {ones₁ : List Term}
    (hb : settleItems o me f₂ b = .value b')
    (h₁ : settleItems o me f₁ ⟨c * b.coefficient, items₁, ones₁⟩ = .value p)
    (hi₁ : items₁.Perm (items₀ ++ b.items)) (ho : ∀ x ∈ b.ones, x ∈ ones₁) :
    ∃ q : ProductParts, p.coefficient = c * b'.coefficient * q.coefficient ∧
      (∀ x, x ∈ p.ones ↔ x ∈ ones₁ ∨ x ∈ b'.ones ∨ x ∈ q.ones) ∧
      ∀ {f₃ : ℕ} {c₃ : ℚ} {items₃ : List (Term × ℤ)} {ones₃ : List Term} {p' : ProductParts},
        settleItems o me f₃ ⟨c₃, items₃, ones₃⟩ = .value p' → items₃.Perm (items₀ ++ b'.items) →
        p'.coefficient = c₃ * q.coefficient ∧ p'.items = p.items ∧
          ∀ x, x ∈ p'.ones ↔ x ∈ ones₃ ∨ x ∈ q.ones := by
  obtain ⟨D, hD⟩ : ∃ D, ∀ x ∈ items₀ ++ b.items, x.1.depth ≤ D := ⟨_, depth_bound _⟩
  have hb' := (settle_out hK f₂ hb fun x hx => hD x (List.mem_append_right _ hx)).1
  have e₁ := settle_nf hK h₁ fun x hx => hD x (hi₁.subset hx)
  have ex := ctx hK f₂ hb c items₀ [] hD
  have a₁ := nf_perm (o := o) hK D hi₁
  rw [nf_scale _ (c * b.coefficient)] at e₁ ex; rw [nf_scale _ (c * b'.coefficient)] at ex
  simp only [Equiv, List.mem_append, List.not_mem_nil, false_or] at e₁ ex a₁
  have := hK.1
  refine ⟨nf o D ⟨1, items₀ ++ b'.items, []⟩, by rw [← e₁.1, a₁.1, ex.1], fun x => ?_,
    fun {f₃ c₃ items₃ ones₃ p'} h₃ hi₃ => ?_⟩
  · have := e₁.2.2 x; have := a₁.2.2 x; have := ex.2.2 x; have := ho x; tauto
  have e₃ := settle_nf hK h₃ fun x hx => by
    rcases List.mem_append.1 (hi₃.subset hx) with hx | hx
    exacts [hD x (List.mem_append_left _ hx), (hb' x hx).2]
  have a₃ := nf_perm (o := o) hK D hi₃
  rw [nf_scale _ c₃] at e₃
  simp only [Equiv, List.mem_append] at e₃ a₃
  refine ⟨by rw [← e₃.1, a₃.1], eq_of_strictlyIncreasing_map (fun x : Term × ℤ => Key.of x.1 x.2)
    (settleItems_items hK h₃).2 (settleItems_items hK h₁).2 fun x =>
      (e₃.2.1.symm.trans (a₃.2.1.trans (ex.2.1.symm.trans (a₁.2.1.symm.trans e₁.2.1)))).mem_iff,
    fun x => ?_⟩
  have := e₃.2.2 x; have := a₃.2.2 x; tauto

/-- Reducing one item first: the rounds of the items `x :: L`, and those of
the items with `x` replaced by its reduction `(r, back)`, whose settled parts
join the coefficient and the ones, give the same coefficient, items and ones. -/
public theorem settleItems_reduceItem {o : Orders} (hK : TotalCmp (Key.cmp o)) {me f₁ f₂ : ℕ}
    {c : ℚ} {x : Term × ℤ} {L back : List (Term × ℤ)} {ones : List Term} {r p p' : ProductParts}
    (hr : reduceItem me x = .value (r, back))
    (h₁ : settleItems o me f₁ ⟨c, x :: L, ones⟩ = .value p)
    (h₂ : settleItems o me f₂ ⟨c * r.coefficient, r.items ++ back ++ L, ones ++ r.ones⟩ =
      .value p') :
    p'.coefficient = p.coefficient ∧ p'.items = p.items ∧ ∀ z, z ∈ p'.ones ↔ z ∈ p.ones := by
  obtain ⟨rfl, rfl⟩ : r = (ured x).1 ∧ back = (ured x).2 := by
    simpa [Prod.ext_iff] using reduceItem_value hr
  obtain ⟨D, hD⟩ : ∃ D, ∀ y ∈ x :: L, y.1.depth ≤ D := ⟨_, depth_bound _⟩
  have e₁ := settle_nf hK h₁ hD
  have e₂ := settle_nf hK h₂ fun y hy => by
    rcases List.mem_append.1 hy with hy | hy
    exacts [(ured_depth x y hy).trans (hD x (by simp)), hD y (by simp [hy])]
  have er := reduce_any hK x D c L ones (hD x (by simp))
  have := hK.1
  exact ⟨e₂.1.symm.trans (er.1.symm.trans e₁.1), eq_of_strictlyIncreasing_map
    (fun y : Term × ℤ => Key.of y.1 y.2) (settleItems_items hK h₂).2 (settleItems_items hK h₁).2
      fun y => (e₂.2.1.symm.trans (er.2.1.symm.trans e₁.2.1)).mem_iff,
    fun z => (e₂.2.2 z).symm.trans ((er.2.2 z).symm.trans (e₁.2.2 z))⟩

/-! ## Parts that settle alike -/

/-- Parts that settle alike: under every large enough bound `D` on the depths and in
every context `L` of items no deeper than `D`, the normal forms have the same
coefficient, and the same items up to order where it is not 0. The ones are not read. -/
public def SettleEq (o : Orders) (p q : ProductParts) : Prop :=
  ∃ D₀, ∀ D, D₀ ≤ D → ∀ L : List (Term × ℤ), (∀ x ∈ L, x.1.depth ≤ D) →
    p.coefficient * (nf o D ⟨1, L ++ p.items, []⟩).coefficient =
      q.coefficient * (nf o D ⟨1, L ++ q.items, []⟩).coefficient ∧
    (p.coefficient * (nf o D ⟨1, L ++ p.items, []⟩).coefficient ≠ 0 →
      (nf o D ⟨1, L ++ p.items, []⟩).items.Perm (nf o D ⟨1, L ++ q.items, []⟩).items)

/-- `SettleEq` is transitive. -/
public theorem SettleEq.trans {p q r : ProductParts} (h : SettleEq o p q) (h' : SettleEq o q r) :
    SettleEq o p r :=
  let ⟨D₁, h⟩ := h; let ⟨D₂, h'⟩ := h'
  ⟨max D₁ D₂, fun D hD L hL =>
    let a := h D (le_of_max_le_left hD) L hL; let b := h' D (le_of_max_le_right hD) L hL
    ⟨a.1.trans b.1, fun e => (a.2 e).trans (b.2 (a.1 ▸ e))⟩⟩

/-- Parts with the same coefficient and the same items up to order settle alike. -/
public theorem SettleEq.of_perm (hK : TotalCmp (Key.cmp o)) {p q : ProductParts}
    (hc : p.coefficient = q.coefficient) (hi : p.items.Perm q.items) : SettleEq o p q :=
  ⟨0, fun D _ L _ => let e := nf_perm hK D (hi.append_left L); ⟨by rw [hc, e.1], fun _ => e.2.1⟩⟩

/-- Parts that settle like parts with the coefficient 0 settle like any such parts. -/
public theorem SettleEq.zero {p q r : ProductParts} (h : SettleEq o p q)
    (hq : q.coefficient = 0) (hr : r.coefficient = 0) : SettleEq o p r :=
  let ⟨D₀, h⟩ := h
  ⟨D₀, fun D hD L hL => by
    have e := (h D hD L hL).1; rw [hq, zero_mul] at e; rw [hr, zero_mul]
    exact ⟨e, fun h' => absurd e h'⟩⟩

/-- Parts settle like the parts that their rounds return. -/
public theorem SettleEq.of_settle (hK : TotalCmp (Key.cmp o)) {me f : ℕ} {c : ℚ}
    {items : List (Term × ℤ)} {os : List Term} {p' : ProductParts}
    (h : settleItems o me f ⟨c, items, os⟩ = .value p') (os' : List Term) :
    SettleEq o ⟨c, items, os'⟩ p' :=
  ⟨Term.depthList (items.map Prod.fst), fun D hD L hL => by
    have e := ctx hK f h 1 L [] fun x hx =>
      (List.mem_append.1 hx).elim (hL x) fun hx => (depth_bound _ x hx).trans hD
    rw [nf_scale D (1 * c), nf_scale D (1 * p'.coefficient)] at e
    exact ⟨by simpa using e.1, fun _ => e.2.1⟩⟩

/-- One item settles like its reduction. -/
public theorem SettleEq.reduce (hK : TotalCmp (Key.cmp o)) {me : ℕ} {x : Term × ℤ}
    {r : ProductParts × List (Term × ℤ)} (h : reduceItem me x = .value r) (os os' : List Term) :
    SettleEq o ⟨1, [x], os⟩ ⟨r.1.coefficient, r.1.items ++ r.2, os'⟩ := by
  obtain rfl := reduceItem_value h
  refine ⟨x.1.depth, fun D hD L _ => ?_⟩
  have e := (nf_perm hK D (List.perm_append_comm (l₁ := L) (l₂ := [x]))).trans
    (reduce_any hK x D 1 L [] hD)
  rw [nf_scale D (1 * _)] at e
  have e' := nf_perm (o := o) hK D (List.perm_append_comm (l₁ := (ured x).1.items ++ (ured x).2)
    (l₂ := L))
  exact ⟨by rw [one_mul, e.1, e'.1, one_mul], fun _ => e.2.1.trans e'.2.1⟩

/-- Parts that settle alike, joined, settle alike. -/
public theorem SettleEq.append (hK : TotalCmp (Key.cmp o)) {p q p' q' : ProductParts}
    (h : SettleEq o p q) (h' : SettleEq o p' q') : SettleEq o (p.append p') (q.append q') := by
  obtain ⟨D₁, h⟩ := h; obtain ⟨D₂, h'⟩ := h'
  refine ⟨max (max D₁ D₂) (max (Term.depthList (p'.items.map Prod.fst))
    (Term.depthList (q.items.map Prod.fst))), fun D hD L hL => ?_⟩
  simp only [max_le_iff] at hD
  have hb : ∀ M : List (Term × ℤ), Term.depthList (M.map Prod.fst) ≤ D →
      ∀ x ∈ L ++ M, x.1.depth ≤ D := fun M hM x hx =>
    (List.mem_append.1 hx).elim (hL x) fun hx => (depth_bound M x hx).trans hM
  obtain ⟨a1, a2⟩ := h D hD.1.1 _ (hb _ hD.2.1)
  obtain ⟨b1, b2⟩ := h' D hD.1.2 _ (hb _ hD.2.2)
  have e1 := nf_perm (o := o) hK D (show (L ++ (p.items ++ p'.items)).Perm (L ++ p'.items ++ p.items)
    by rw [List.append_assoc]; exact List.perm_append_comm.append_left L)
  have e2 := nf_perm (o := o) hK D (show (L ++ p'.items ++ q.items).Perm (L ++ q.items ++ p'.items)
    by simp only [List.append_assoc]; exact List.perm_append_comm.append_left L)
  simp only [ProductParts.append, ← List.append_assoc] at e1 ⊢
  have c1 := e1.1; have c2 := e2.1
  refine ⟨by linear_combination p.coefficient * p'.coefficient * c1 + p'.coefficient * a1 +
    q.coefficient * p'.coefficient * c2 + q.coefficient * b1, fun hn => ?_⟩
  have hn1 : p.coefficient * (nf o D ⟨1, L ++ p'.items ++ p.items, []⟩).coefficient ≠ 0 :=
    fun e => hn (by linear_combination p'.coefficient * e + p.coefficient * p'.coefficient * c1)
  have hn2 : p'.coefficient * (nf o D ⟨1, L ++ q.items ++ p'.items, []⟩).coefficient ≠ 0 :=
    fun e => hn (by linear_combination p.coefficient * p'.coefficient * c1 + p'.coefficient * a1 +
      q.coefficient * p'.coefficient * c2 + q.coefficient * e)
  exact e1.2.1.trans ((a2 hn1).trans (e2.2.1.trans (b2 hn2)))

/-- Folds of parts that settle alike, one by one, settle alike. -/
public theorem SettleEq.foldl (hK : TotalCmp (Key.cmp o)) : ∀ {Xs Ys : List ProductParts},
    List.Forall₂ (SettleEq o) Xs Ys → ∀ {p q : ProductParts}, SettleEq o p q →
      SettleEq o (Xs.foldl ProductParts.append p) (Ys.foldl ProductParts.append q)
  | _, _, .nil, _, _, h => h
  | _, _, .cons hx hs, _, _, h => SettleEq.foldl hK hs (h.append hK hx)

/-- The rounds of parts that settle alike return the same coefficient, and the same
items where it is not 0. -/
public theorem SettleEq.settle (hK : TotalCmp (Key.cmp o)) {me f f' : ℕ} {p q ρ ρ' : ProductParts}
    (h : SettleEq o p q) {os os' : List Term}
    (hp : settleItems o me f ⟨p.coefficient, p.items, os⟩ = .value ρ)
    (hq : settleItems o me f' ⟨q.coefficient, q.items, os'⟩ = .value ρ') :
    ρ.coefficient = ρ'.coefficient ∧ (ρ.coefficient ≠ 0 → ρ.items = ρ'.items) := by
  obtain ⟨D₀, h⟩ := h
  have hd := le_max_right D₀ (max (Term.depthList (p.items.map Prod.fst))
    (Term.depthList (q.items.map Prod.fst)))
  have e := settle_nf hK hp fun x hx => (depth_bound _ x hx).trans ((le_max_left _ _).trans hd)
  have e' := settle_nf hK hq fun x hx => (depth_bound _ x hx).trans ((le_max_right _ _).trans hd)
  rw [nf_scale] at e e'
  obtain ⟨h1, h2⟩ := h _ (le_max_left _ _) [] (by simp)
  simp only [List.nil_append] at h1 h2
  have := hK.1
  exact ⟨e.1.symm.trans (h1.trans e'.1), fun hc => eq_of_strictlyIncreasing_map
    (fun x : Term × ℤ => Key.of x.1 x.2) (settleItems_items hK hp).2 (settleItems_items hK hq).2
    fun x => (e.2.1.symm.trans ((h2 fun h0 => hc (e.1.symm.trans h0)).trans e'.2.1)).mem_iff⟩

end Kalyx.Proofs.Terms.Settle
