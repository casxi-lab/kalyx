module

public import Kalyx.Statements.Terms
public import Kalyx.Proofs.Terms.Basics
public import Kalyx.Proofs.Terms.Sorting
public import Kalyx.Proofs.Terms.Order
public import Kalyx.Proofs.Terms.Bases

/-!
# Products: order, limits, rounds and merging

The product conjuncts of `SumsAndProductsIgnoreOrderAndGrouping` but grouping, and
those of `MergingAddsCoefficientsAndExponents` but the powers of roots, which
`Kalyx.Proofs.Terms.Grouping` proves: a product ignores the order of its operands, a
product of values succeeds or fails with `ResourceLimit` naming `max_exponent` (the rounds
of `settleItems` always suffice), and keeps its value under a larger limit; a product of
canonical operands without roots of a literal degree and with a coefficient other than 0
keeps the coefficient up to the sign of the power of `i` and the total exponent of every
other key; the zero witness and the held ones are kept; and `i ^ k` is `i` to the power `k`
modulo 4. The read-back of a built product (`productParts_finish`) is exported, with the shape of the
items of canonical values kept by the rounds (`RootShape`, `settleItems_shape`) and the
assembly of settled parts (`finish_eq`).
-/

namespace Kalyx.Proofs.Terms.Products

open Kalyx.Spec.Terms Kalyx.Statements.Terms Kalyx.Proofs.Terms

variable {α β : Type}

/-! ## Results -/

/-- A value, or `ResourceLimit` naming `max_exponent`. -/
private def VL (r : Result α) : Prop := (∃ v, r = .value v) ∨ r = .resourceLimit .exponent
/-- A bind of values or limits. -/
private theorem VL.bind {x : Result α} {f : α → Result β} (hx : VL x)
    (hf : ∀ v, x = .value v → VL (f v)) : VL (x >>= f) := by
  rcases hx with ⟨v, rfl⟩ | rfl; exacts [hf v rfl, .inr rfl]
/-- A check of an exponent before a value or a limit. -/
private theorem VL.check {me : ℕ} {k : ℤ} {next : Unit → Result α} (h : VL (next ())) :
    VL (checkExponent me k next) := by
  unfold checkExponent; split; exacts [.inr rfl, h]
/-- `mapM` of values or limits. -/
private theorem VL.mapM {f : α → Result β} : ∀ {l : List α}, (∀ a ∈ l, VL (f a)) → VL (l.mapM f)
  | [], _ => .inl ⟨[], rfl⟩
  | a :: l, h => by
    rw [List.mapM_cons]
    exact (h a (by simp)).bind fun _ _ =>
      (VL.mapM fun x hx => h x (.tail _ hx)).bind fun _ _ => .inl ⟨_, rfl⟩
/-- A `mapM` whose function gives values. -/
private theorem mapM_eq_map {f : α → Result β} {g : α → β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = .value (g a)) → l.mapM f = .value (l.map g)
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mapM_cons, h a (by simp), mapM_eq_map fun x hx => h x (.tail _ hx)]; rfl
/-- Related lists whose relation is a function. -/
public theorem forall₂_map {R : α → β → Prop} {g : α → β} :
    ∀ {l : List α} {rs : List β}, List.Forall₂ R l rs → (∀ a ∈ l, ∀ r, R a r → r = g a) →
      rs = l.map g
  | _, _, .nil, _ => rfl
  | _, _, .cons h hs, hg => by
    rw [List.map_cons, hg _ (by simp) _ h, forall₂_map hs fun a ha => hg a (.tail _ ha)]
/-- A `mapM` that fails on an element of values or limits is the limit. -/
private theorem mapM_limit {f : α → Result β} (h : ∀ a, VL (f a)) {a : α}
    (hn : ∀ v, f a ≠ .value v) : ∀ {l : List α}, a ∈ l → l.mapM f = .resourceLimit .exponent
  | b :: l, hm => by
    rw [List.mapM_cons]
    rcases h b with ⟨v, hv⟩ | hv
    · rcases List.mem_cons.1 hm with rfl | hm
      · exact absurd hv (hn v)
      · rw [hv, bind_value, mapM_limit h hn hm]; rfl
    · rw [hv]; rfl
/-- `mapM` of values `g` or limits over two permuted lists. -/
private theorem mapM_perm {f : α → Result β} {g : α → β} (h : ∀ a, VL (f a))
    (hg : ∀ a r, f a = .value r → r = g a) {l l' : List α} (hp : l.Perm l') :
    (l.mapM f = .resourceLimit .exponent ∧ l'.mapM f = .resourceLimit .exponent) ∨
      (l.mapM f = .value (l.map g) ∧ l'.mapM f = .value (l'.map g)) := by
  by_cases hall : ∀ a ∈ l, ∃ v, f a = .value v
  · have e : ∀ a ∈ l, f a = .value (g a) := fun a ha => by
      obtain ⟨v, hv⟩ := hall a ha; rw [hv, ← hg a v hv]
    exact .inr ⟨mapM_eq_map e, mapM_eq_map fun a ha => e a (hp.mem_iff.2 ha)⟩
  · simp only [not_forall, not_exists] at hall
    obtain ⟨a, ha, hn⟩ := hall
    exact .inl ⟨mapM_limit h hn ha, mapM_limit h hn (hp.mem_iff.1 ha)⟩
/-- `r'` has the value of `r`, when `r` has one. -/
private def Up (r r' : Result α) : Prop := ∀ v, r = .value v → r' = .value v
/-- A bind of results that keep their values. -/
private theorem Up.bind {x x' : Result α} {f f' : α → Result β} (hx : Up x x')
    (hf : ∀ a, Up (f a) (f' a)) : Up (x >>= f) (x' >>= f') := fun v h => by
  obtain ⟨a, ha, hfa⟩ := bind_eq_value.1 h; rw [hx a ha]; exact hf a v hfa
/-- `mapM` of results that keep their values. -/
private theorem Up.mapM {f f' : α → Result β} (h : ∀ a, Up (f a) (f' a)) :
    ∀ l : List α, Up (l.mapM f) (l.mapM f')
  | [] => fun _ h => h
  | a :: l => by
    rw [List.mapM_cons, List.mapM_cons]
    exact (h a).bind fun _ => (Up.mapM h l).bind fun _ _ h => h
/-- A larger limit keeps the value of a check. -/
private theorem Up.check {me me' : ℕ} (hle : me ≤ me') {k : ℤ} {n n' : Unit → Result α}
    (h : Up (n ()) (n' ())) : Up (checkExponent me k n) (checkExponent me' k n') := fun v hv => by
  unfold checkExponent at hv ⊢
  have : exponentBound me ≤ exponentBound me' := min_le_min_right _ hle
  split at hv; · cases hv
  rw [ite_eq_right (by omega)]; exact h v hv
/-- A larger limit keeps the value of either branch. -/
private theorem Up.ite {c : Prop} [Decidable c] {a a' b b' : Result α} (ha : Up a a')
    (hb : Up b b') : Up (if c then a else b) (if c then a' else b') := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h]; exact ha
  · rw [ite_eq_right h, ite_eq_right h]; exact hb

/-! ## Parts without checks -/

/-- `itemParts` without the check of its exponent. -/
@[expose] public def uItem (q : ℤ) : Term → ProductParts
  | .sum c ms => ⟨sumContent c ms ^ q, [(primitivePart c ms, q)], []⟩
  | .power b j => if j = 0 then ⟨1, [], [.power b j]⟩ else ⟨1, [(b, j * q)], []⟩
  | t => ⟨1, [(t, q)], []⟩
/-- `factorParts` without the checks of exponents. -/
@[expose] public def uFactor (q : ℤ) : Term → ProductParts
  | .number r => ⟨r ^ q, [], []⟩
  | .product c fs => (fs.map (uItem q)).foldl ProductParts.append ⟨c ^ q, [], []⟩
  | t => uItem q t
/-- The value of `itemParts` is `uItem`. -/
public theorem itemParts_eq {me : ℕ} {q : ℤ} {t : Term} {r : ProductParts}
    (h : itemParts me q t = .value r) : r = uItem q t := by
  cases t <;> simp only [itemParts, uItem, checkExponent] at h ⊢ <;>
    try exact (Result.value.inj h).symm
  split_ifs at h ⊢ <;> cases h <;> rfl
/-- The value of `factorParts` is `uFactor`. -/
public theorem factorParts_eq {me : ℕ} {q : ℤ} {t : Term} {r : ProductParts}
    (h : factorParts me q t = .value r) : r = uFactor q t := by
  cases t with
  | number => exact (Result.value.inj h).symm
  | product c fs =>
    obtain ⟨ps, hps, h⟩ := bind_eq_value.1 h
    rw [← Result.value.inj h, uFactor, forall₂_map (mapM_value hps) fun a _ r hr => itemParts_eq hr]
  | _ => simp only [factorParts, uFactor] at h ⊢; exact itemParts_eq h
/-- `itemParts` gives a value or the limit. -/
private theorem itemParts_vl (me : ℕ) (q : ℤ) (t : Term) : VL (itemParts me q t) := by
  cases t <;> simp only [itemParts] <;> try exact .inl ⟨_, rfl⟩
  split; exacts [.inl ⟨_, rfl⟩, VL.check (.inl ⟨_, rfl⟩)]
/-- `factorParts` gives a value or the limit. -/
private theorem factorParts_vl (me : ℕ) (q : ℤ) (t : Term) : VL (factorParts me q t) := by
  cases t <;> simp only [factorParts] <;> first
    | exact .inl ⟨_, rfl⟩
    | exact itemParts_vl me q _
    | exact (VL.mapM fun x _ => itemParts_vl me q x).bind fun _ _ => .inl ⟨_, rfl⟩
/-- A larger limit keeps the value of `itemParts`. -/
private theorem itemParts_up {me me' : ℕ} (hle : me ≤ me') (q : ℤ) (t : Term) :
    Up (itemParts me q t) (itemParts me' q t) := by
  cases t <;> simp only [itemParts] <;> try exact fun _ h => h
  split; exacts [fun _ h => h, Up.check hle fun _ h => h]
/-- A larger limit keeps the value of `factorParts`. -/
private theorem factorParts_up {me me' : ℕ} (hle : me ≤ me') (q : ℤ) (t : Term) :
    Up (factorParts me q t) (factorParts me' q t) := by
  cases t <;> simp only [factorParts] <;> first
    | exact fun _ h => h
    | exact itemParts_up hle q _
    | exact (Up.mapM (itemParts_up hle q) _).bind fun _ _ h => h
/-- A larger limit keeps the value of `reduceItem`. -/
private theorem reduceItem_up {me me' : ℕ} (hle : me ≤ me') (x : Term × ℤ) :
    Up (reduceItem me x) (reduceItem me' x) := by
  obtain ⟨b, k⟩ := x
  unfold reduceItem
  refine Up.check hle (Up.ite (fun _ h => h) (Up.ite (fun _ h => h) ?_))
  rcases rootOf b with _ | ⟨u, n⟩
  · exact fun _ h => h
  · exact Up.ite ((factorParts_up hle _ _).bind fun _ _ h => h) fun _ h => h

/-! ## Rounds -/

/-- The term that `buildProduct` assembles from settled parts. -/
@[expose] public def finish (o : Orders) (p : ProductParts) : Term :=
  if p.coefficient = 0 then
    zeroWitness (maxBases o (Term.negBasesList (p.items.map itemFactor ++ p.ones)))
  else
    assembleProduct p.coefficient (sortBy (fun f g => Key.cmp o f.key g.key)
      (p.items.map itemFactor ++ (maxBases o (uncovered (Term.negBasesList p.ones)
        (Term.negBasesList (p.items.map itemFactor)))).map Term.oneOf))
/-- One round of `settleItems`. -/
public theorem settleItems_succ (o : Orders) (me fuel : ℕ) (p : ProductParts) :
    settleItems o me (fuel + 1) p = (mergeItems o p.items).mapM (reduceItem me) >>= fun rs =>
      if (rs.map Prod.snd).flatten.isEmpty then
        .value ⟨p.coefficient * (rs.map (·.1.coefficient)).prod, (rs.map (·.1.items)).flatten,
          p.ones ++ (rs.map (·.1.ones)).flatten⟩
      else settleItems o me fuel ⟨p.coefficient * (rs.map (·.1.coefficient)).prod,
        (rs.map (·.1.items)).flatten ++ (rs.map Prod.snd).flatten,
        p.ones ++ (rs.map (·.1.ones)).flatten⟩ := by
  rw [settleItems]; congr 1; funext rs
  have := foldl_append (rs.map Prod.fst) ⟨p.coefficient, [], p.ones⟩
  rw [List.foldl_map] at this
  simp only [this, List.map_map, List.nil_append]; rfl
/-- A larger limit keeps the value of `settleItems`. -/
private theorem settleItems_up {o : Orders} {me me' : ℕ} (hle : me ≤ me') :
    ∀ (fuel : ℕ) (p : ProductParts), Up (settleItems o me fuel p) (settleItems o me' fuel p)
  | 0, _ => fun _ h => h
  | fuel + 1, p => by
    rw [settleItems_succ, settleItems_succ]
    exact (Up.mapM (reduceItem_up hle) _).bind fun rs =>
      Up.ite (fun _ h => h) (settleItems_up hle fuel _)
/-- The ones of the parts are carried through the rounds. -/
private theorem settleItems_ones (o : Orders) (me : ℕ) : ∀ (fuel : ℕ) (c : ℚ)
    (items : List (Term × ℤ)) (ones : List Term),
    settleItems o me fuel ⟨c, items, ones⟩ = (settleItems o me fuel ⟨c, items, []⟩).map
      fun s => ⟨s.coefficient, s.items, ones ++ s.ones⟩
  | 0, _, _, _ => rfl
  | fuel + 1, c, items, ones => by
    rw [settleItems_succ, settleItems_succ]
    rcases (mergeItems o items).mapM (reduceItem me) with rs | _ | _ <;> try rfl
    simp only [bind_value]; split
    · simp [Result.map]
    · rw [settleItems_ones o me fuel _ _ (ones ++ _), settleItems_ones o me fuel _ _ ([] ++ _)]
      cases settleItems o me fuel _ <;> simp [Result.map]
/-- The rounds of a product, with its ones set aside, and the assembly. -/
public theorem buildProduct_eq (o : Orders) (me : ℕ) (p : ProductParts) :
    buildProduct o me p = (settleItems o me (Term.depthList (p.items.map Prod.fst) + 1)
      ⟨p.coefficient, p.items, []⟩).map
        fun s => finish o ⟨s.coefficient, s.items, p.ones ++ s.ones⟩ := by
  obtain ⟨c, items, ones⟩ := p
  rw [buildProduct, settleItems_ones]
  rcases settleItems o me _ ⟨c, items, []⟩ with v | _ | _ <;> try rfl
  simp only [Result.map, bind_value, finish]; split <;> rfl
/-- `N` of two lists together. -/
private theorem mem_negBasesList_append {b : Term} {l l' : List Term} :
    b ∈ Term.negBasesList (l ++ l') ↔ b ∈ Term.negBasesList l ∨ b ∈ Term.negBasesList l' := by
  simp only [mem_negBasesList, List.mem_append, or_and_right, exists_or]
/-- The assembly reads the ones only through the bases they hold that the factors do not. -/
private theorem finish_congr {o : Orders} (hT : TotalCmp (Term.cmp o)) {c : ℚ}
    {its : List (Term × ℤ)} {os os' : List Term}
    (h : ∀ b, b ∈ Term.negBasesList os ∨ b ∈ Term.negBasesList (its.map itemFactor) ↔
      b ∈ Term.negBasesList os' ∨ b ∈ Term.negBasesList (its.map itemFactor)) :
    finish o ⟨c, its, os⟩ = finish o ⟨c, its, os'⟩ := by
  unfold finish; dsimp only; split
  · rw [maxBases_congr hT (bs' := Term.negBasesList (its.map itemFactor ++ os')) fun b => by
      rw [mem_negBasesList_append, mem_negBasesList_append, or_comm, h, or_comm]]
  · rw [maxBases_congr hT (bs := uncovered (Term.negBasesList os) _)
      (bs' := uncovered (Term.negBasesList os') (Term.negBasesList (its.map itemFactor)))
      fun b => by
        have := h b; simp only [uncovered, List.mem_filter, Bool.not_eq_true', Bool.eq_false_iff,
          ne_eq, List.contains_iff_mem]; tauto]
/-- The largest depth of a list is a bound on each term. -/
public theorem depthList_le {n : ℕ} :
    ∀ {ts : List Term}, Term.depthList ts ≤ n ↔ ∀ t ∈ ts, t.depth ≤ n
  | [] => by simp [Term.depthList]
  | t :: ts => by simp [Term.depthList, depthList_le]
/-- `settleItems` merges the items first, so it does not depend on their order. -/
private theorem settleItems_perm {o : Orders} (hK : TotalCmp (Key.cmp o)) (me fuel : ℕ) (c : ℚ)
    {items items' : List (Term × ℤ)} (os : List Term) (hp : items.Perm items') :
    settleItems o me fuel ⟨c, items, os⟩ = settleItems o me fuel ⟨c, items', os⟩ := by
  cases fuel; · rfl
  simp only [settleItems_succ, mergeItems_perm hK hp]

/-! ## Order and limits -/

/-- The parts of the operands of a product, the first and the rest. -/
public theorem productParts_cons (me : ℕ) (t : Term) (ts : List Term) :
    productParts me (t :: ts) = factorParts me 1 t >>= fun r => (productParts me ts).map fun p =>
      ⟨r.coefficient * p.coefficient, r.items ++ p.items, r.ones ++ p.ones⟩ := by
  unfold productParts; rw [List.mapM_cons]
  rcases factorParts me 1 t with r | _ | _ <;> try rfl
  cases ts.mapM (factorParts me 1) <;> simp [foldl_append, ProductParts.unit, Result.map]
/-- The parts of permuted operands. -/
private theorem productParts_perm (me : ℕ) {ts ts' : List Term} (hp : ts.Perm ts') :
    (productParts me ts = .resourceLimit .exponent ∧
        productParts me ts' = .resourceLimit .exponent) ∨
      ∃ p p', productParts me ts = .value p ∧ productParts me ts' = .value p' ∧
        p.coefficient = p'.coefficient ∧ p.items.Perm p'.items ∧ p.ones.Perm p'.ones := by
  unfold productParts
  rcases mapM_perm (factorParts_vl me 1) (fun _ _ => factorParts_eq) hp with ⟨h, h'⟩ | ⟨h, h'⟩
  · rw [h, h']; exact .inl ⟨rfl, rfl⟩
  have hr := hp.map (uFactor 1)
  rw [h, h']; refine .inr ⟨_, _, rfl, rfl, ?_⟩; simp only [foldl_append]
  exact ⟨by rw [(hr.map _).prod_eq], ((hr.map _).flatten).append_left _,
    ((hr.map _).flatten).append_left _⟩
/-- A product does not depend on the order of its operands. -/
public theorem mkProduct_perm (o : Orders) (ho : o.Total) (me : ℕ) {ts ts' : List Term}
    (hp : ts.Perm ts') : mkProduct o me ts = mkProduct o me ts' := by
  unfold mkProduct; rw [hp.any_eq]; split; · rfl
  rcases productParts_perm me hp with ⟨h, h'⟩ | ⟨p, p', h, h', hc, hi, hn⟩
  · rw [h, h']
  have hd := hi.map Prod.fst
  rw [h, h', bind_value, bind_value, buildProduct_eq, buildProduct_eq, hc,
    settleItems_perm (keyCmp_total o ho) _ _ _ _ hi,
    le_antisymm (depthList_le.2 fun t ht => depthList_le.1 le_rfl t (hd.mem_iff.1 ht))
      (depthList_le.2 fun t ht => depthList_le.1 le_rfl t (hd.mem_iff.2 ht))]
  congr 1; funext s
  exact finish_congr (termCmp_total o ho) fun b => by
    simp only [mem_negBasesList, (hn.append_right s.ones).mem_iff]
/-- A product that succeeds under a limit gives the same term under a larger one. -/
public theorem mkProduct_mono {o : Orders} {me me' : ℕ} {ts : List Term} {u : Term}
    (h : mkProduct o me ts = .value u) (hle : me ≤ me') : mkProduct o me' ts = .value u := by
  unfold mkProduct at h ⊢
  split at h; · cases h
  rw [ite_eq_right ‹_›]
  refine ((Up.mapM (factorParts_up hle 1) ts).bind fun _ _ h => h).bind (fun p => ?_) u h
  unfold buildProduct; exact (settleItems_up hle _ _).bind fun _ _ h => h

/-! ## Reductions and the fuel of the rounds -/

/-- The key of an item. -/
private abbrev ky (x : Term × ℤ) : Key := Key.of x.1 x.2
/-- The cases of a merged item that `reduceItem` reduces. -/
public theorem reduceItem_cases {me : ℕ} {b : Term} {k : ℤ} {r : ProductParts × List (Term × ℤ)}
    (h : reduceItem me (b, k) = .value r) :
    (k = 0 ∧ r = (ProductParts.unit, [])) ∨
    (k ≠ 0 ∧ b = Term.imaginaryUnit ∧ r = (⟨if k % 4 = 2 ∨ k % 4 = 3 then -1 else 1,
        if k % 4 = 1 ∨ k % 4 = 3 then [(b, 1)] else [], []⟩, [])) ∨
    (k ≠ 0 ∧ b ≠ Term.imaginaryUnit ∧ ∃ u n, rootOf b = some (u, n) ∧ (n : ℤ) ≤ k ∧
      r = (⟨(uFactor (k / n) u).coefficient, if k % n = 0 then [] else [(b, k % n)],
        (uFactor (k / n) u).ones⟩, (uFactor (k / n) u).items)) ∨
    (k ≠ 0 ∧ b ≠ Term.imaginaryUnit ∧ (∀ u n, rootOf b = some (u, n) → k < n) ∧
      r = (⟨1, [(b, k)], []⟩, [])) := by
  rw [reduceItem] at h; unfold checkExponent at h
  split at h; · cases h
  by_cases hk : k = 0
  · rw [ite_eq_left hk] at h; exact .inl ⟨hk, (Result.value.inj h).symm⟩
  rw [ite_eq_right hk] at h
  by_cases hb : b = Term.imaginaryUnit
  · rw [ite_eq_left hb] at h; exact .inr (.inl ⟨hk, hb, (Result.value.inj h).symm⟩)
  rw [ite_eq_right hb] at h; right; right
  rcases hr : rootOf b with _ | ⟨u, n⟩ <;> rw [hr] at h
  · exact .inr ⟨hk, hb, (fun _ _ e => nomatch e), (Result.value.inj h).symm⟩
  dsimp only at h
  by_cases hn : (n : ℤ) ≤ k
  · rw [ite_eq_left hn] at h
    obtain ⟨p, hp, h⟩ := bind_eq_value.1 h
    exact .inl ⟨hk, hb, u, n, rfl, hn, by rw [← factorParts_eq hp]; exact (Result.value.inj h).symm⟩
  · rw [ite_eq_right hn] at h
    exact .inr ⟨hk, hb, (fun u' n' e => by cases e; omega), (Result.value.inj h).symm⟩
/-- `reduceItem` gives a value or the limit. -/
private theorem reduceItem_vl (me : ℕ) (x : Term × ℤ) : VL (reduceItem me x) := by
  obtain ⟨b, k⟩ := x
  unfold reduceItem; refine VL.check ?_; dsimp only
  repeat' split
  all_goals first
    | exact .inl ⟨_, rfl⟩
    | exact (factorParts_vl me _ _).bind fun _ _ => .inl ⟨_, rfl⟩
/-- The scaled monomials of a primitive part have the same depth. -/
private theorem depthPairs_map (a : ℚ) :
    ∀ ms : List (ℚ × Term), Term.depthPairs (ms.map fun m => (a * m.1, m.2)) = Term.depthPairs ms
  | [] => rfl
  | (_, t) :: ms => by simp only [List.map_cons, Term.depthPairs, depthPairs_map a ms]
/-- What holds of the items of `uItem` of the term, or of each factor, holds of `uFactor`. -/
private theorem uFactor_items {q : ℤ} {P : Term × ℤ → Prop} {t : Term}
    (h : ∀ s, (s = t ∧ (∀ r, t ≠ .number r) ∧ ∀ c fs, t ≠ .product c fs) ∨
      (∃ c fs, t = .product c fs ∧ s ∈ fs) → ∀ y ∈ (uItem q s).items, P y) :
    ∀ y ∈ (uFactor q t).items, P y := by
  cases t with
  | number => simp [uFactor]
  | product c fs =>
    simp only [uFactor, foldl_append, List.nil_append, List.mem_flatten, List.mem_map]
    rintro y ⟨_, ⟨_, ⟨f, hf, rfl⟩, rfl⟩, hy⟩
    exact h f (.inr ⟨c, fs, rfl, hf⟩) y hy
  | _ => exact h _ (.inl ⟨rfl, nofun, nofun⟩)
/-- The items of `uFactor` lie no deeper than the term, with exponents other than 0. -/
public theorem uFactor_depth {q : ℤ} (hq : q ≠ 0) (t : Term) :
    ∀ y ∈ (uFactor q t).items, y.1.depth ≤ t.depth ∧ y.2 ≠ 0 :=
  uFactor_items fun s hs y hy => by
    have : y.1.depth ≤ s.depth ∧ y.2 ≠ 0 := by
      cases s <;> simp only [uItem] at hy <;> (try split at hy) <;>
        simp_all [primitivePart, scaleSum, Term.depth, depthPairs_map]
    refine ⟨this.1.trans ?_, this.2⟩
    rcases hs with ⟨rfl, -, -⟩ | ⟨c, fs, rfl, hf⟩
    · exact le_rfl
    · have := depthList_le.1 le_rfl s hf; simp only [Term.depth]; omega
/-- A merged item that the rounds leave as it is. -/
@[expose] public def Settled (x : Term × ℤ) : Prop :=
  x.2 ≠ 0 ∧ (x.1 = Term.imaginaryUnit → x.2 = 1) ∧ ∀ u n, rootOf x.1 = some (u, n) → x.2 < n
/-- A reduced item: at most one settled item of its key, and shallower returning items. -/
private theorem reduceItem_out {me : ℕ} {x : Term × ℤ} {r : ProductParts × List (Term × ℤ)}
    (h : reduceItem me x = .value r) :
    (r.1.items = [] ∨ ∃ y, r.1.items = [y] ∧ Settled y ∧ ky y = ky x) ∧
      (∀ y ∈ r.2, y.1.depth < x.1.depth ∧ y.2 ≠ 0) ∧ (Settled x → r.2 = []) := by
  obtain ⟨b, k⟩ := x
  rcases reduceItem_cases h with ⟨hk, rfl⟩ | ⟨hk, rfl, rfl⟩ | ⟨hk, hb, u, n, hr, hn, rfl⟩ |
    ⟨hk, hb, hr, rfl⟩
  · exact ⟨.inl rfl, by simp, fun _ => rfl⟩
  · dsimp only; refine ⟨?_, by simp, fun _ => rfl⟩; split
    · exact .inr ⟨_, rfl, ⟨one_ne_zero, fun _ => rfl, fun _ _ e => nomatch e⟩,
        by simp [Key.of, Term.imaginaryUnit, Term.isConstant]⟩
    · exact .inl rfl
  · obtain ⟨h2, hd, rest, rfl, -⟩ := rootOf_some hr
    have h1 : 1 ≤ k / n := Int.le_ediv_of_mul_le (by omega) (by omega)
    have := Int.emod_nonneg k (by omega : (n : ℤ) ≠ 0)
    dsimp only
    refine ⟨?_, fun y hy => ?_, fun hs => absurd (hs.2.2 u n hr) (by dsimp only; omega)⟩
    · split; · exact .inl rfl
      refine .inr ⟨_, rfl, ⟨‹_›, fun e => absurd e hb, fun u' n' e => ?_⟩, ?_⟩
      · rw [hr] at e; cases e; exact Int.emod_lt_of_pos _ (by omega)
      · show Key.of _ (k % n) = Key.of _ k
        simp only [Key.of, show ¬k % n < 0 by omega, show ¬k < 0 by omega, decide_false,
          Bool.false_and]
    · obtain ⟨d1, d2⟩ := uFactor_depth (q := k / n) (by omega) u y hy
      have := le_max_left u.depth (Term.depthList rest)
      exact ⟨by simp only [Term.depth, Term.depthList]; omega, d2⟩
  · exact ⟨.inr ⟨_, rfl, ⟨hk, fun e => absurd e hb, hr⟩, rfl⟩, by simp, fun _ => rfl⟩
/-- The total exponent of a key over two lists. -/
public theorem exponentOf_append (K : Key) (a b : List (Term × ℤ)) :
    exponentOf K (a ++ b) = exponentOf K a + exponentOf K b := by
  simp [exponentOf, List.filter_append]
/-- The total exponent of a key over an item and a list. -/
public theorem exponentOf_cons (K : Key) (y : Term × ℤ) (l : List (Term × ℤ)) :
    exponentOf K (y :: l) = (if Key.of y.1 y.2 = K then y.2 else 0) + exponentOf K l := by
  simp only [exponentOf, List.filter_cons]; split <;> simp_all
/-- The total exponent of a key that no item has is 0. -/
public theorem exponentOf_eq_zero {K : Key} {l : List (Term × ℤ)} (h : K ∉ l.map fun y => Key.of y.1 y.2) :
    exponentOf K l = 0 := by
  rw [exponentOf, List.filter_eq_nil_iff.2 fun y hy e =>
    h (List.mem_map.2 ⟨y, hy, of_decide_eq_true e⟩)]; rfl
/-- The total exponent of the key of an item, among items of distinct keys. -/
private theorem exponentOf_single : ∀ {l : List (Term × ℤ)}, (l.map ky).Nodup → ∀ {s}, s ∈ l →
    exponentOf (ky s) l = s.2
  | y :: l, hN, s, hs => by
    rw [List.map_cons, List.nodup_cons] at hN; rw [exponentOf_cons]
    rcases List.mem_cons.1 hs with rfl | hs
    · rw [ite_eq_left rfl, exponentOf_eq_zero hN.1, add_zero]
    · rw [ite_eq_right fun e => hN.1 (by rw [show ky y = ky s from e]; exact List.mem_map_of_mem hs),
        exponentOf_single hN.2 hs, zero_add]
/-- A merged item whose key no new item has is a settled item. -/
private theorem merged_mem_left {o : Orders} (hK : TotalCmp (Key.cmp o))
    {S B : List (Term × ℤ)} (hN : (S.map ky).Nodup) {x : Term × ℤ}
    (hx : x ∈ mergeItems o (S ++ B)) (hb : ky x ∉ B.map ky) : x ∈ S := by
  obtain ⟨hk, he⟩ := (mem_mergeItems hK).1 hx
  rw [List.map_append, List.mem_append] at hk
  obtain ⟨y, hy, e⟩ := List.mem_map.1 (hk.resolve_right hb)
  rw [exponentOf_append, exponentOf_eq_zero hb, add_zero, ← e, exponentOf_single hN hy] at he
  rwa [show x = y from Prod.ext (congrArg Key.base e).symm he]
/-- The settled items of a round have keys among the merged keys. -/
private theorem sublist_keys {me : ℕ} : ∀ {M : List (Term × ℤ)}
    {rs : List (ProductParts × List (Term × ℤ))},
    List.Forall₂ (fun x r => reduceItem me x = .value r) M rs →
      ((rs.map (·.1.items)).flatten.map ky).Sublist (M.map ky)
  | _, _, .nil => by simp
  | x :: _, _ :: _, .cons h hs => by
    simp only [List.map_cons, List.flatten_cons, List.map_append]
    refine List.Sublist.append (l₂ := [ky x]) ?_ (sublist_keys hs)
    rcases (reduceItem_out h).1 with e | ⟨y, e, -, hy⟩ <;> rw [e] <;> simp [*]
/-- The next round: settled items, and items returning from merged items not settled. -/
private theorem next_items {me : ℕ} {M : List (Term × ℤ)}
    {rs : List (ProductParts × List (Term × ℤ))}
    (hr : ∀ r ∈ rs, ∃ x ∈ M, reduceItem me x = .value r) :
    (∀ y ∈ (rs.map (·.1.items)).flatten, Settled y) ∧
      ∀ y ∈ (rs.map Prod.snd).flatten, ∃ x ∈ M, ¬Settled x ∧ y.1.depth < x.1.depth ∧ y.2 ≠ 0 := by
  simp only [List.mem_flatten, List.mem_map]
  refine ⟨?_, ?_⟩ <;> rintro y ⟨_, ⟨r, hr', rfl⟩, hy⟩ <;> obtain ⟨x, hx, hxr⟩ := hr r hr' <;>
    obtain ⟨h1, h2, h3⟩ := reduceItem_out hxr
  · rcases h1 with e | ⟨y', e, hs, -⟩ <;> rw [e] at hy
    · cases hy
    · rw [List.mem_singleton.1 hy]; exact hs
  · exact ⟨x, hx, (fun hs => by rw [h3 hs] at hy; simp at hy), h2 y hy⟩
/-- The rounds succeed or reach the limit: `S` settled, `B` shallower than the fuel. -/
private theorem settleItems_vl {o : Orders} (hK : TotalCmp (Key.cmp o)) (me : ℕ) :
    ∀ (fuel : ℕ) (c : ℚ) (S B : List (Term × ℤ)) (os : List Term), (∀ x ∈ S, Settled x) →
      (S.map ky).Nodup → (∀ x ∈ B, x.1.depth < fuel) → 0 < fuel →
      VL (settleItems o me fuel ⟨c, S ++ B, os⟩)
  | fuel + 1, c, S, B, os, hS, hN, hB, _ => by
    rw [settleItems_succ]
    refine (VL.mapM fun x _ => reduceItem_vl me x).bind fun rs hrs => ?_
    obtain ⟨hS', hB'⟩ := next_items (mapM_mem hrs).2
    split; · exact .inl ⟨_, rfl⟩
    rename_i hne
    have hback : ∀ y ∈ (rs.map Prod.snd).flatten, y.1.depth < fuel := fun y hy => by
      obtain ⟨x, hx, hns, hd, -⟩ := hB' y hy
      obtain ⟨z, hz, hzx⟩ := List.mem_map.1 (show ky x ∈ B.map ky from Classical.byContradiction
        fun hnot => hns (hS x (merged_mem_left hK hN hx hnot)))
      have := hB z hz; rw [show z.1 = x.1 from congrArg Key.base hzx] at this; omega
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil ((rs.map Prod.snd).flatten)
      fun e => hne (by rw [e]; rfl)
    have := hK.1
    exact settleItems_vl hK me fuel _ _ _ _ hS' ((sublist_keys (mapM_value hrs)).nodup
      (nodup_of_pairwise_lt (strictlyIncreasing_iff_pairwise.1
        (mergeItems_strictlyIncreasing hK _)))) hback (by have := hback y hy; omega)
/-- `buildProduct` succeeds or fails with `ResourceLimit` naming `max_exponent`. -/
public theorem buildProduct_value_or_limit (o : Orders) (ho : o.Total) (me : ℕ) (p : ProductParts) :
    (∃ u, buildProduct o me p = .value u) ∨ buildProduct o me p = .resourceLimit .exponent := by
  obtain ⟨c, items, os⟩ := p
  have h := settleItems_vl (keyCmp_total o ho) me (Term.depthList (items.map Prod.fst) + 1) c []
    items os (by simp) (by simp) (fun x hx => by
      have := depthList_le.1 le_rfl x.1 (List.mem_map_of_mem hx); omega) (Nat.succ_pos _)
  rw [List.nil_append] at h
  exact h.bind fun _ _ => by split <;> exact .inl ⟨_, rfl⟩
/-- A product of values succeeds or fails with `ResourceLimit` naming `max_exponent`. -/
public theorem mkProduct_value_or_limit (o : Orders) (ho : o.Total) (me : ℕ) {ts : List Term}
    (hv : ∀ t ∈ ts, t.isCondition = false) :
    (∃ u, mkProduct o me ts = .value u) ∨ mkProduct o me ts = .resourceLimit .exponent := by
  unfold mkProduct
  rw [ite_eq_right (by
    simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true]; exact hv)]
  exact ((VL.mapM fun t _ => factorParts_vl me 1 t).bind fun _ _ => .inl ⟨_, rfl⟩).bind
    fun p _ => buildProduct_value_or_limit o ho me p

/-! ## Bases of negative powers through the rounds -/

/-- `N` of the factor of an item is `N` of its power. -/
private theorem negBases_itemFactor (y : Term × ℤ) :
    (itemFactor y).negBases = (Term.power y.1 y.2).negBases := by
  unfold itemFactor; split
  · rw [negBases_power_pos (by omega)]
  · rfl
/-- `N` of the factors of items is `N` of their powers. -/
private theorem negBasesList_itemFactor (L : List (Term × ℤ)) :
    Term.negBasesList (L.map itemFactor) = Term.negBasesList (L.map fun y => Term.power y.1 y.2) := by
  induction L with
  | nil => rfl
  | cons y L ih => simp only [List.map_cons, Term.negBasesList, negBases_itemFactor, ih]
/-- The items of the parts of the operands of a product. -/
private theorem productParts_items {me : ℕ} {ts : List Term} {p : ProductParts}
    (h : productParts me ts = .value p) : ∀ y ∈ p.items, ∃ t ∈ ts, y ∈ (uFactor 1 t).items := by
  obtain ⟨ps, hps, h⟩ := bind_eq_value.1 h
  rw [← Result.value.inj h, forall₂_map (mapM_value hps) fun t _ r hr => factorParts_eq hr]
  intro y hy; rw [mem_items_foldl] at hy; simpa [ProductParts.unit] using hy
/-- A positive sum of a list of the sign of `s`. -/
private theorem sum_sign (s : ℤ) : ∀ {l : List ℤ}, l ≠ [] → (∀ z ∈ l, 0 < s * z) → 0 < s * l.sum
  | [a], _, h => by simpa using h a (by simp)
  | a :: b :: l, _, h => by
    have h1 := h a (by simp)
    have h2 := sum_sign s (l := b :: l) (by simp) fun z hz => h z (.tail _ hz)
    rw [List.sum_cons, mul_add]; linarith
/-- A merged item has the base, and off constants the sign, of an item of its key. -/
private theorem mergeItems_base {o : Orders} (hK : TotalCmp (Key.cmp o)) {items : List (Term × ℤ)}
    (hz : ∀ y ∈ items, y.2 ≠ 0) {x : Term × ℤ} (hx : x ∈ mergeItems o items) :
    ∃ y ∈ items, y.1 = x.1 ∧ (x.1.isConstant = false → x.2 ≠ 0 ∧ (x.2 < 0 ↔ y.2 < 0)) := by
  obtain ⟨hk, he⟩ := (mem_mergeItems hK).1 hx
  obtain ⟨y, hy, hyx⟩ := List.mem_map.1 hk
  have hyx1 : y.1 = x.1 := congrArg Key.base hyx
  refine ⟨y, hy, hyx1, fun hc => ?_⟩
  have hy1 : y.1.isConstant = false := by rw [hyx1]; exact hc
  have hs := sum_sign (if y.2 < 0 then -1 else 1)
    (l := (items.filter fun z => Key.of z.1 z.2 = Key.of x.1 x.2).map Prod.snd)
    (List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_filter.2 ⟨hy, decide_eq_true hyx⟩))) (by
      simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
      rintro _ ⟨z, ⟨hz', e⟩, rfl⟩
      have := hz z hz'; have h1 := congrArg Key.negative (e.trans hyx.symm)
      have hz1 : z.1 = y.1 := congrArg Key.base (e.trans hyx.symm)
      simp only [Key.of, hz1, hy1, Bool.not_false, Bool.and_true, decide_eq_decide] at h1
      split_ifs <;> omega)
  rw [exponentOf] at he; rw [← he] at hs
  split_ifs at hs <;> exact ⟨by omega, fun _ => by omega, fun _ => by omega⟩
/-- The coefficient 0 stays through the rounds. -/
public theorem settleItems_coeff {o : Orders} {me : ℕ} : ∀ {fuel : ℕ} {p s : ProductParts},
    settleItems o me fuel p = .value s → p.coefficient = 0 → s.coefficient = 0
  | fuel + 1, p, s, h, hc => by
    rw [settleItems_succ] at h
    obtain ⟨rs, -, h⟩ := bind_eq_value.1 h
    split at h
    · cases h; simp [hc]
    · exact settleItems_coeff h (by simp [hc])

/-! ## Zero coefficients, ones and powers of `i` -/

/-- `N` of the settled factors and of the ones is that of the factors of the items and of
the ones. -/
public theorem settle_N {o : Orders} {me fuel : ℕ} {p s : ProductParts}
    (hz : ∀ y ∈ p.items, y.2 ≠ 0)
    (hs : settleItems o me fuel ⟨p.coefficient, p.items, []⟩ = .value s) (b : Term) :
    b ∈ Term.negBasesList (s.items.map itemFactor ++ (p.ones ++ s.ones)) ↔
      b ∈ Term.negBasesList (p.items.map itemFactor ++ p.ones) := by
  have h := Bases.settleItems_negBases hs hz b
  simp only [partsTerms, List.append_nil, mem_negBasesList_append, negBasesList_itemFactor] at h ⊢
  tauto
/-- `N` of the settled factors and of all the ones of a product is that of its operands. -/
public theorem settled_N {o : Orders} {me fuel : ℕ} {ts : List Term}
    {p s : ProductParts} (hp : productParts me ts = .value p)
    (hs : settleItems o me fuel ⟨p.coefficient, p.items, []⟩ = .value s) (b : Term) :
    b ∈ Term.negBasesList (s.items.map itemFactor ++ (p.ones ++ s.ones)) ↔
      b ∈ Term.negBasesList ts := by
  obtain ⟨hz, hN⟩ := Bases.productParts_negBases hp
  rw [settle_N hz hs, ← hN, partsTerms, mem_negBasesList_append, mem_negBasesList_append,
    negBasesList_itemFactor]
/-- A product of values: its operands are values, its parts and their assembly. -/
public theorem mkProduct_split {o : Orders} {me : ℕ} {ts : List Term} {u : Term}
    (h : mkProduct o me ts = .value u) : (∀ t ∈ ts, t.isCondition = false) ∧
      ∃ P, productParts me ts = .value P ∧ buildProduct o me P = .value u := by
  unfold mkProduct at h; split at h; · cases h
  rename_i hv; simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at hv
  exact ⟨hv, bind_eq_value.1 h⟩
/-- A product with the coefficient 0 is the zero witness of the bases of its operands. -/
public theorem mkProduct_zero (o : Orders) (ho : o.Total) (me : ℕ) {ts : List Term} {u : Term}
    (h : mkProduct o me (.number 0 :: ts) = .value u) :
    u = zeroWitness (maxBases o (Term.negBasesList ts)) := by
  obtain ⟨-, p, hp, h⟩ := mkProduct_split h
  rw [buildProduct_eq] at h
  obtain ⟨s, hs, rfl⟩ := map_eq_value.1 h
  have hc : p.coefficient = 0 := by
    have hp' := hp; rw [productParts_cons] at hp'
    obtain ⟨r, hr, hp'⟩ := bind_eq_value.1 hp'
    obtain ⟨p', -, rfl⟩ := map_eq_value.1 hp'
    cases hr; simp
  unfold finish; dsimp only; rw [ite_eq_left (settleItems_coeff hs hc)]
  have := settled_N hp hs
  simp only [Term.negBasesList, Term.negBases, List.nil_append] at this
  rw [maxBases_congr (termCmp_total o ho) this]
/-- A one `(b⁻¹)⁰` whose base the other operands hold in `N` does not change a product. -/
public theorem mkProduct_one (o : Orders) (ho : o.Total) (me : ℕ) {b : Term} {ts : List Term}
    (hb : b ∈ Term.negBasesList ts) : mkProduct o me (b.oneOf :: ts) = mkProduct o me ts := by
  unfold mkProduct
  rw [show (b.oneOf :: ts).any Term.isCondition = ts.any Term.isCondition by
    simp [Term.oneOf, Term.isCondition]]
  split; · rfl
  rw [productParts_cons, show factorParts me 1 b.oneOf = .value ⟨1, [], [b.oneOf]⟩ from rfl,
    bind_value]
  rcases hp : productParts me ts with p | _ | _ <;> try rfl
  simp only [Result.map, bind_value, buildProduct_eq, one_mul, List.nil_append]
  rcases hs : settleItems o me _ ⟨p.coefficient, p.items, []⟩ with s | _ | _ <;> try rfl
  dsimp only; congr 1
  refine finish_congr (termCmp_total o ho) fun x => ?_
  have := settled_N hp hs x
  rw [mem_negBasesList_append] at this
  have hx : x ∈ b.oneOf.negBases → x ∈ Term.negBasesList ts := fun hx => by
    obtain ⟨t, ht, hbt⟩ := mem_negBasesList.1 hb
    refine mem_negBasesList.2 ⟨t, ht, ?_⟩
    have : x = b ∨ x ∈ b.negBases := by simp [Term.oneOf, Term.negBases] at hx; tauto
    rcases this with rfl | hx; exacts [hbt, negBases_trans hbt hx]
  simp only [List.cons_append, Term.negBasesList, List.mem_append]
  tauto
/-- `i ^ k` is `i` to the power `k` modulo 4, the sign in the coefficient. -/
public theorem mkPower_imaginaryUnit (o : Orders) (me : ℕ) {k : ℤ}
    (hk : k.natAbs ≤ exponentBound me) : mkPower o me Term.imaginaryUnit k = .value (iPower k) := by
  have hb : ¬exponentBound me < k.natAbs := by omega
  unfold mkPower checkExponent; rw [ite_eq_right hb]
  by_cases h1 : k = 1; · subst h1; rfl
  by_cases h0 : k = 0; · subst h0; rfl
  have hm : mergeItems o [(.constant (.named .i), k)] = [(.constant (.named .i), k)] := rfl
  have hr : reduceItem me (.constant (.named .i), k) = .value (⟨if k % 4 = 2 ∨ k % 4 = 3 then -1
      else 1, if k % 4 = 1 ∨ k % 4 = 3 then [(.constant (.named .i), 1)] else [], []⟩, []) := by
    have e : Term.constant (.named .i) = Term.imaginaryUnit := rfl
    rw [reduceItem, checkExponent, ite_eq_right hb, ite_eq_right h0, ite_eq_left e]
  unfold Term.imaginaryUnit
  simp only [Term.isCondition, h1, h0, distributedPower, mergedPower, mergePowers, buildProduct_eq,
    Term.depthList, List.map, Term.depth, settleItems_succ, hm, List.mapM_cons, List.mapM_nil, hr,
    bind_value, Bool.false_eq_true, ite_false, pure_value, List.flatten_cons, List.flatten_nil,
    List.isEmpty_nil, ite_true, Result.map, List.append_nil, List.prod_cons, List.prod_nil, mul_one,
    one_mul, List.nil_append]
  have : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases this with h | h | h | h <;> simp [h, finish, assembleProduct, iPower, itemFactor, maxBases,
    uncovered, sortedTerms, Term.negBasesList, sortBy, insertBy, mergeAdjacent, Term.imaginaryUnit]
  norm_num

/-! ## Merging without roots -/

/-- An item whose factor reads back as the item: an exponent other than 0, a base
that can be a factor, and a negative exponent over a power. -/
@[expose] public def ItemShape (x : Term × ℤ) : Prop :=
  x.2 ≠ 0 ∧ x.1.factorOk = true ∧ ∀ c j, x.1 = .power c j → x.2 < 0
/-- A sum of content 1 scaled by `c ≠ 0` reads back as `c` and the sum. -/
private theorem uItem_scaleSum {c a : ℚ} {ms : List (ℚ × Term)} (hc : c ≠ 0)
    (h : sumContent a ms = 1) : uItem 1 (scaleSum c a ms) = ⟨c, [(.sum a ms, 1)], []⟩ := by
  simp [scaleSum, uItem, primitivePart, sumContent_scale hc, h, List.map_map, Function.comp_def, hc]
/-- The factor of an item of that shape can be a factor, and reads back as the item. -/
private theorem uItem_itemFactor {x : Term × ℤ} (h : ItemShape x) :
    uItem 1 (itemFactor x) = ⟨1, [x], []⟩ ∧ (itemFactor x).factorOk = true := by
  obtain ⟨b, k⟩ := x
  obtain ⟨h0, hf, hp⟩ := h
  unfold itemFactor; dsimp only at *; split
  · subst k
    cases b with
    | sum a ms =>
      have := uItem_scaleSum one_ne_zero (by simpa [Term.factorOk] using hf)
      simp only [scaleSum, one_mul] at this; simp_all
    | power c j => exact absurd (hp c j rfl) (by omega)
    | _ => simp_all [uItem]
  · simp [uItem, h0, Term.factorOk]
/-- A built product with a coefficient other than 0 reads back its coefficient and items. -/
public theorem productParts_finish (o : Orders) (me : ℕ) {s q : ProductParts}
    (hc : s.coefficient ≠ 0) (hs : ∀ x ∈ s.items, ItemShape x)
    (hq : productParts me [finish o s] = .value q) :
    q.coefficient = s.coefficient ∧ q.items.Perm s.items := by
  have hq' : factorParts me 1 (finish o s) >>= (fun r => .value
      (⟨r.coefficient * 1, r.items ++ [], r.ones ++ []⟩ : ProductParts)) = .value q := by
    rw [← hq, productParts_cons]; rfl
  obtain ⟨r, hr, hq⟩ := bind_eq_value.1 hq'
  cases hq; rw [factorParts_eq hr, mul_one, List.append_nil]
  obtain ⟨c, its, os⟩ := s
  dsimp only at hc hs ⊢; unfold finish; dsimp only; rw [ite_eq_right hc]
  have hL := perm_sortBy (fun f g : Term => Key.cmp o f.key g.key) (its.map itemFactor ++
    (maxBases o (uncovered (Term.negBasesList os) (Term.negBasesList (its.map itemFactor)))).map
      Term.oneOf)
  generalize sortBy _ _ = L at hL
  have hu : ∀ f ∈ L, (uItem 1 f).coefficient = 1 ∧ f.factorOk = true := fun f hf => by
    rcases List.mem_append.1 (hL.mem_iff.1 hf) with hf | hf <;>
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hf
    · exact ⟨by rw [(uItem_itemFactor (hs x hx)).1], (uItem_itemFactor (hs x hx)).2⟩
    · simp [uItem, Term.oneOf, Term.factorOk]
  have hI : (L.map fun f => (uItem 1 f).items).flatten.Perm its := by
    refine (hL.map _).flatten.trans ?_
    rw [List.map_append, List.flatten_append, List.map_map, List.map_congr_left fun x hx => by
      rw [Function.comp_apply, (uItem_itemFactor (hs x hx)).1]]
    have e : ∀ l : List (Term × ℤ), (l.map fun x => [x]).flatten = l := fun l => by
      induction l <;> simp_all
    simp [Function.comp_def, Term.oneOf, uItem, e]
  have hC : (L.map fun f => (uItem 1 f).coefficient).prod = 1 :=
    List.prod_eq_one fun _ h => by obtain ⟨f, hf, rfl⟩ := List.mem_map.1 h; exact (hu f hf).1
  have hP : (uFactor 1 (.product c L)).coefficient = c ∧
      (uFactor 1 (.product c L)).items.Perm its := by
    simp only [uFactor, foldl_append, List.map_map, Function.comp_def, hC, zpow_one, mul_one,
      List.nil_append]
    exact ⟨trivial, hI⟩
  rcases L with _ | ⟨f, _ | ⟨g, rest⟩⟩
  · simp only [List.map_nil, List.flatten_nil, List.nil_perm] at hI
    simp [assembleProduct, uFactor, hI]
  · obtain ⟨h1, hf⟩ := hu f (by simp)
    have hfi : (uItem 1 f).items.Perm its := by simpa using hI
    simp only [assembleProduct]; split_ifs with hc1
    · rw [show uFactor 1 f = uItem 1 f by cases f <;> simp_all [uFactor, Term.factorOk]]
      exact ⟨h1.trans hc1.symm, hfi⟩
    · cases f with
      | sum a ms =>
        have ha : sumContent a ms = 1 := by simpa [Term.factorOk] using hf
        have := uItem_scaleSum one_ne_zero ha; simp [scaleSum] at this
        rw [show uFactor 1 (scaleSum c a ms) = uItem 1 (scaleSum c a ms) from rfl,
          uItem_scaleSum hc ha]
        rw [this] at hfi; exact ⟨rfl, hfi⟩
      | _ => exact hP
  · exact hP
/-- The items of a canonical value that is no condition read back as themselves. -/
private theorem uFactor_shape {o : Orders} {me : ℕ} {R : RegistryRules} {t : Term}
    (ht : Term.Canonical o me R t) (hv : t.isCondition = false) :
    ∀ y ∈ (uFactor 1 t).items, ItemShape y := by
  have hok : ∀ x ∈ t.nodes, x.nodeOk o me R = true := List.all_eq_true.1 ht.1
  refine uFactor_items fun s hs y hy => ?_
  obtain ⟨hn, hf⟩ : s.nodeOk o me R = true ∧ (s.factorOk = true ∨ ∃ c ms, s = .sum c ms) := by
    rcases hs with ⟨rfl, h1, h2⟩ | ⟨c, fs, rfl, hf⟩
    · exact ⟨hok _ (mem_nodes_self _), by cases s <;> simp_all [Term.factorOk, Term.isCondition]⟩
    · have h := hok _ (mem_nodes_self _)
      simp only [Term.nodeOk, canonicalProduct, Bool.and_eq_true, List.all_eq_true] at h
      exact ⟨hok s (by rw [Term.nodes]; exact .tail _ (mem_nodesList.2 ⟨s, hf, mem_nodes_self s⟩)),
        .inl (h.1.1.1 s hf)⟩
  cases s with
  | sum c ms =>
    simp only [uItem, List.mem_singleton] at hy; subst hy
    have hne := sumContent_ne_zero (o := o) (by simpa [Term.nodeOk] using hn)
    refine ⟨one_ne_zero, ?_, fun _ _ h => nomatch h⟩
    simp [Term.factorOk, primitivePart, scaleSum, sumContent_scale (inv_ne_zero hne), hne]
  | power b j =>
    simp only [uItem] at hy; split at hy; · simp at hy
    simp only [List.mem_singleton] at hy; subst hy
    simp only [Term.nodeOk, canonicalPower, Bool.and_eq_true] at hn
    refine ⟨by simpa, hn.1.1.1.1, fun c i e => ?_⟩
    subst e
    have h2 : mergeCondition i j = false := by
      have := hn.2; simp only [Bool.and_eq_true, Bool.not_eq_true'] at this; exact this.1
    have := mergeCondition_false.1 h2; dsimp only; omega
  | _ => simp only [uItem, List.mem_singleton] at hy; subst hy; simp_all [ItemShape, Term.factorOk]
/-- The reduction of a merged item that is no root: dropped at 0, `i` modulo 4, or kept. -/
private def red (x : Term × ℤ) : ProductParts :=
  if x.2 = 0 then ProductParts.unit else if x.1 = Term.imaginaryUnit then
    ⟨if x.2 % 4 = 2 ∨ x.2 % 4 = 3 then -1 else 1,
      if x.2 % 4 = 1 ∨ x.2 % 4 = 3 then [(x.1, 1)] else [], []⟩
  else ⟨1, [x], []⟩
/-- `reduceItem` of an item that is no root. -/
private theorem reduceItem_red {me : ℕ} {x : Term × ℤ} {r : ProductParts × List (Term × ℤ)}
    (hn : rootOf x.1 = none) (h : reduceItem me x = .value r) : r = (red x, []) := by
  obtain ⟨b, k⟩ := x
  rcases reduceItem_cases h with ⟨hk, rfl⟩ | ⟨hk, rfl, rfl⟩ | ⟨-, -, u, n, hr, -⟩ | ⟨hk, hb, -, rfl⟩
  · simp [red, hk]
  · simp [red, hk]
  · rw [hn] at hr; cases hr
  · simp [red, hk, hb]
/-- `red` of an item over `i`. -/
private theorem red_i (k : ℤ) : red (Term.imaginaryUnit, k) =
    ⟨if k % 4 = 2 ∨ k % 4 = 3 then -1 else 1,
      if k % 4 = 1 ∨ k % 4 = 3 then [(Term.imaginaryUnit, 1)] else [], []⟩ := by
  by_cases h : k = 0 <;> simp [red, h, ProductParts.unit]
/-- `red` of an item over another base. -/
private theorem red_ne {x : Term × ℤ} (h : x.1 ≠ Term.imaginaryUnit) :
    (red x).coefficient = 1 ∧ (red x).items = if x.2 = 0 then [] else [x] := by
  unfold red; by_cases h0 : x.2 = 0 <;> simp [h0, h, ProductParts.unit]
/-- The total exponent of a key over a `flatMap`. -/
public theorem exponentOf_flatMap (K : Key) (g : α → List (Term × ℤ)) :
    ∀ M : List α, exponentOf K (M.flatMap g) = (M.map fun x => exponentOf K (g x)).sum
  | [] => rfl
  | x :: M => by simp [exponentOf_append, exponentOf_flatMap K g M]
/-- The product of operands whose items are no roots, with a coefficient other than 0,
keeps the coefficient and the total exponent of every key but that of `i`, whose total
`e` returns to `i ^ (e mod 4)`. -/
public theorem mkProduct_parts (o : Orders) (ho : o.Total) {me : ℕ} {R : RegistryRules}
    {ts : List Term} {u : Term} {p q : ProductParts} (hcan : ∀ t ∈ ts, Term.Canonical o me R t)
    (hp : productParts me ts = .value p) (hroot : ∀ x ∈ p.items, rootOf x.1 = none)
    (hc : p.coefficient ≠ 0) (hu : mkProduct o me ts = .value u)
    (hq : productParts me [u] = .value q) :
    let e := exponentOf (Key.of Term.imaginaryUnit 1) p.items
    q.coefficient = p.coefficient * (if e % 4 = 2 ∨ e % 4 = 3 then -1 else 1) ∧
      exponentOf (Key.of Term.imaginaryUnit 1) q.items = (if e % 2 = 1 then 1 else 0) ∧
      ∀ K, K.base ≠ Term.imaginaryUnit → exponentOf K q.items = exponentOf K p.items := by
  have hK := keyCmp_total o ho; intro e
  obtain ⟨hv, p', hp', hu⟩ := mkProduct_split hu; rw [hp] at hp'; cases hp'
  rw [buildProduct_eq, settleItems_succ] at hu
  obtain ⟨s, hs, rfl⟩ := map_eq_value.1 hu
  obtain ⟨rs, hrs, hs⟩ := bind_eq_value.1 hs
  have hpi : ∀ y ∈ p.items, ItemShape y := fun y hy => by
    obtain ⟨t, ht, hy⟩ := productParts_items hp y hy
    exact uFactor_shape (hcan t ht) (hv t ht) y hy
  have hbase := fun x (hx : x ∈ mergeItems o p.items) =>
    mergeItems_base hK (fun y hy => (hpi y hy).1) hx
  rw [forall₂_map (mapM_value hrs) fun x hx r hr => reduceItem_red (by
    obtain ⟨y, hy, e, -⟩ := hbase x hx; rw [← e]; exact hroot y hy) hr] at hs
  simp [List.map_map, Function.comp_def] at hs
  subst hs
  set M := mergeItems o p.items
  have := hK.1
  have hN : M.Nodup := (nodup_of_pairwise_lt (strictlyIncreasing_iff_pairwise.1
    (mergeItems_strictlyIncreasing hK _))).of_map _
  have hki : ∀ k, Key.of Term.imaginaryUnit k = Key.of Term.imaginaryUnit 1 := fun k => by
    simp [Key.of, Term.imaginaryUnit, Term.isConstant]
  have hMi : ∀ x ∈ M, x.1 = Term.imaginaryUnit → x = (Term.imaginaryUnit, e) :=
    fun x hx h => Prod.ext h (by rw [((mem_mergeItems hK).1 hx).2, h, hki])
  have he0 : (Term.imaginaryUnit, e) ∉ M → e = 0 := fun hn => by
    by_contra h0
    have : Key.of Term.imaginaryUnit 1 ∈ p.items.map ky := by
      by_contra hk; exact h0 (exponentOf_eq_zero hk)
    obtain ⟨x, hx, hxk⟩ := List.mem_map.1 ((mem_keys_mergeItems hK _ _).2 this)
    exact hn (hMi x hx (congrArg Key.base hxk) ▸ hx)
  have hcoef : (M.map fun x => (red x).coefficient).prod =
      if e % 4 = 2 ∨ e % 4 = 3 then -1 else 1 := by
    rw [List.prod_map_eq_pow_single (Term.imaginaryUnit, e) _ fun x hne hx =>
      (red_ne fun h => hne (hMi x hx h)).1]
    by_cases hm : (Term.imaginaryUnit, e) ∈ M
    · rw [List.count_eq_one_of_mem hN hm, pow_one, red_i]
    · rw [List.count_eq_zero_of_not_mem hm, pow_zero, he0 hm]; simp
  have hiexp : exponentOf (Key.of Term.imaginaryUnit 1) (M.map fun x => (red x).items).flatten =
      if e % 2 = 1 then 1 else 0 := by
    rw [← List.flatMap_def, exponentOf_flatMap,
      List.sum_map_eq_nsmul_single (Term.imaginaryUnit, e) _ fun x hne hx => ?_]
    · by_cases hm : (Term.imaginaryUnit, e) ∈ M
      · rw [List.count_eq_one_of_mem hN hm, one_smul, red_i]
        split_ifs <;> simp [exponentOf] <;> omega
      · rw [List.count_eq_zero_of_not_mem hm, zero_smul, he0 hm]; simp
    · have : x.1 ≠ Term.imaginaryUnit := fun h => hne (hMi x hx h)
      rw [(red_ne this).2]; split_ifs; · rfl
      simp [exponentOf, Key.of, this]
  have hKexp : ∀ K, K.base ≠ Term.imaginaryUnit →
      exponentOf K (M.map fun x => (red x).items).flatten = exponentOf K p.items := fun K hK' => by
    have e1 : ∀ l : List (Term × ℤ), (l.map fun x => [x]).flatten = l := fun l => by
      induction l <;> simp_all
    rw [← List.flatMap_def, exponentOf_flatMap, ← exponentOf_mergeItems hK p.items K]
    conv_rhs => rw [← e1 (mergeItems o p.items), ← List.flatMap_def, exponentOf_flatMap]
    congr 1
    refine List.map_congr_left fun ⟨b, k⟩ hx => ?_
    have hne : Key.of Term.imaginaryUnit 1 ≠ K := fun h => hK' (congrArg Key.base h).symm
    by_cases h1 : b = Term.imaginaryUnit
    · subst h1; rw [red_i]; split_ifs <;> simp [exponentOf, hki, hne]
    · rw [(red_ne h1).2]; split_ifs with h0; swap; · rfl
      rw [show k = 0 from h0, exponentOf_cons]; simp [exponentOf]
  have hsi : ∀ y ∈ (M.map fun x => (red x).items).flatten, ItemShape y := by
    intro y hy
    obtain ⟨_, hl, hy⟩ := List.mem_flatten.1 hy
    obtain ⟨⟨b, k⟩, hx, rfl⟩ := List.mem_map.1 hl
    by_cases h1 : b = Term.imaginaryUnit
    · subst h1; rw [red_i] at hy; dsimp only at hy; split_ifs at hy; swap; · cases hy
      rw [List.mem_singleton.1 hy]
      exact ⟨one_ne_zero, rfl, fun _ _ h => by simp [Term.imaginaryUnit] at h⟩
    · rw [(red_ne h1).2] at hy; split_ifs at hy with h0; · cases hy
      rw [List.mem_singleton.1 hy]
      obtain ⟨y', hy', e', hs'⟩ := hbase _ hx
      refine ⟨h0, e' ▸ (hpi y' hy').2.1, fun c j hcj => ?_⟩
      exact (hs' (by dsimp only at hcj ⊢; rw [hcj]; rfl)).2.2 ((hpi y' hy').2.2 c j (e'.trans hcj))
  obtain ⟨hq1, hq2⟩ := productParts_finish o me (by rw [hcoef]; split_ifs <;> simp [hc]) hsi hq
  have hperm : ∀ K, exponentOf K q.items = exponentOf K (M.map fun x => (red x).items).flatten :=
    fun K => ((hq2.filter _).map _).sum_eq
  exact ⟨by rw [hq1, hcoef], by rw [hperm, hiexp], fun K hK' => by rw [hperm, hKexp K hK']⟩

/-! ## Read-back of built products -/

/-- An item of the shape `ItemShape` whose base, when it is a root, has a canonical radicand that is
a value. -/
@[expose] public def RootShape (o : Orders) (me : ℕ) (R : RegistryRules) (x : Term × ℤ) : Prop :=
  ItemShape x ∧ ∀ u n, rootOf x.1 = some (u, n) → Term.Canonical o me R u ∧ u.isCondition = false
/-- An item with an exponent other than 0 over a canonical root has that shape. -/
public theorem rootShape_root {o : Orders} {me : ℕ} {R : RegistryRules} {b u : Term} {n : ℕ}
    {k : ℤ} (hb : Term.Canonical o me R b) (h : rootOf b = some (u, n)) (hk : k ≠ 0) :
    RootShape o me R (b, k) := by
  obtain ⟨-, hd, rest, rfl, -⟩ := rootOf_some h
  exact ⟨⟨hk, rfl, nofun⟩, fun _ _ h' => root_radicand hb h'⟩
/-- The items of `uFactor q t` are those of `uFactor 1 t`, their exponents times `q`. -/
private theorem uFactor_scale (q : ℤ) (t : Term) :
    (uFactor q t).items = (uFactor 1 t).items.map fun y => (y.1, y.2 * q) := by
  have hi : ∀ s, (uItem q s).items = (uItem 1 s).items.map fun y => (y.1, y.2 * q) := fun s => by
    cases s <;> simp only [uItem] <;> (try split) <;> simp
  cases t <;> simp [uFactor, foldl_append, hi, List.map_flatten, Function.comp_def]
/-- The items of a positive power of a canonical value have that shape. -/
private theorem uFactor_root {o : Orders} {me : ℕ} {R : RegistryRules} {q : ℤ} {t : Term}
    (hq : 0 < q) (ht : Term.Canonical o me R t) (hv : t.isCondition = false) :
    ∀ y ∈ (uFactor q t).items, RootShape o me R y := by
  have hb : ∀ y ∈ (uFactor 1 t).items, y.1 ∈ t.nodes ∨ rootOf y.1 = none :=
    uFactor_items fun s hs y hy => by
      have hs' : s ∈ t.nodes := by
        rcases hs with ⟨rfl, -, -⟩ | ⟨c, fs, rfl, hf⟩
        exacts [mem_nodes_self _, .tail _ (mem_nodesList.2 ⟨s, hf, mem_nodes_self s⟩)]
      cases s <;> simp only [uItem] at hy <;> (try split at hy) <;>
        simp only [List.mem_singleton, List.not_mem_nil] at hy <;> subst hy <;>
        first | exact .inl hs' | exact .inr rfl | exact .inl (nodes_trans hs' (.tail _ (mem_nodes_self _)))
  rw [uFactor_scale]; rintro _ hz; obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
  obtain ⟨h0, hf, hp⟩ := uFactor_shape ht hv y hy
  refine ⟨⟨mul_ne_zero h0 hq.ne', hf, fun c j e => mul_neg_of_neg_of_pos (hp c j e) hq⟩,
    fun u n hr => ?_⟩
  rcases hb y hy with hn | hn
  · exact (rootShape_root (canonical_node ht hn) hr one_ne_zero).2 u n hr
  · rw [hn] at hr; cases hr
/-- The items of a positive power of a canonical value have that shape. -/
public theorem factorParts_shape {o : Orders} {me me' : ℕ} {R : RegistryRules} {q : ℤ} {t : Term}
    {P : ProductParts} (hq : 0 < q) (ht : Term.Canonical o me R t) (hv : t.isCondition = false)
    (h : factorParts me' q t = .value P) : ∀ y ∈ P.items, RootShape o me R y := by
  rw [factorParts_eq h]; exact uFactor_root hq ht hv
/-- The items of the parts of canonical values have that shape. -/
public theorem productParts_shape {o : Orders} {me me' : ℕ} {R : RegistryRules} {ts : List Term}
    {P : ProductParts} (hts : ∀ t ∈ ts, Term.Canonical o me R t ∧ t.isCondition = false)
    (h : productParts me' ts = .value P) : ∀ y ∈ P.items, RootShape o me R y := fun y hy =>
  let ⟨t, ht, hy⟩ := productParts_items h y hy; uFactor_root one_pos (hts t ht).1 (hts t ht).2 y hy
/-- The rounds keep items of that shape. -/
public theorem settleItems_shape {o : Orders} (hK : TotalCmp (Key.cmp o)) {me me' : ℕ}
    {R : RegistryRules} : ∀ {f : ℕ} {p s : ProductParts}, settleItems o me f p = .value s →
      (∀ x ∈ p.items, RootShape o me' R x) → ∀ x ∈ s.items, RootShape o me' R x
  | f + 1, p, s, h, hp => by
    rw [settleItems_succ] at h
    obtain ⟨rs, hrs, h⟩ := bind_eq_value.1 h
    have hr : ∀ r ∈ rs, ∀ z ∈ r.1.items ++ r.2, RootShape o me' R z := fun r hr' => by
      obtain ⟨⟨b, k⟩, hx, hxr⟩ := (mapM_mem hrs).2 r hr'
      obtain ⟨⟨yb, yk⟩, hy, e, hs⟩ := mergeItems_base hK (fun y hy => (hp y hy).1.1) hx
      obtain ⟨⟨-, hf, hpw⟩, hro⟩ := hp _ hy
      dsimp only at e hs hf hpw hro; subst e
      rcases reduceItem_cases hxr with ⟨-, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, -, u, n, hr, hn, rfl⟩ |
        ⟨hk, -, -, rfl⟩
      · simp [ProductParts.unit]
      · intro z hz; dsimp only at hz; split at hz <;> simp at hz; subst hz
        exact ⟨⟨one_ne_zero, rfl, nofun⟩, nofun⟩
      · obtain ⟨-, hd, rest, rfl, -⟩ := rootOf_some hr
        intro z hz; rcases List.mem_append.1 hz with hz | hz
        · dsimp only at hz; split at hz; · cases hz
          rw [List.mem_singleton.1 hz]; exact ⟨⟨‹_›, hf, nofun⟩, hro⟩
        · obtain ⟨hu, hv⟩ := hro u n hr
          exact uFactor_root (Int.le_ediv_of_mul_le (by have := (rootOf_some hr).1; omega)
            (by omega)) hu hv z hz
      · intro z hz; simp only [List.mem_singleton, List.append_nil] at hz; subst hz
        exact ⟨⟨hk, hf, fun c j e => ((hs (by dsimp only at e; rw [e]; rfl)).2).2 (hpw c j e)⟩, hro⟩
    have hall : ∀ z ∈ (rs.map (·.1.items)).flatten ++ (rs.map Prod.snd).flatten,
        RootShape o me' R z := by
      simp only [List.mem_append, List.mem_flatten, List.mem_map]
      rintro z (⟨_, ⟨r, hr', rfl⟩, hz⟩ | ⟨_, ⟨r, hr', rfl⟩, hz⟩)
      exacts [hr r hr' z (List.mem_append_left _ hz), hr r hr' z (List.mem_append_right _ hz)]
    split at h
    · cases h; exact fun z hz => hall z (List.mem_append_left _ hz)
    · exact settleItems_shape hK h hall
/-- A zero witness reads back with the coefficient 0. -/
public theorem zeroWitness_parts {me : ℕ} {bs : List Term} {A : ProductParts}
    (h : factorParts me 1 (zeroWitness bs) = .value A) : A.coefficient = 0 := by
  unfold zeroWitness at h; split at h
  · cases h; simp
  · obtain ⟨ps, -, h⟩ := bind_eq_value.1 h; cases h; simp [foldl_append]
/-- Assemblies of settled parts with the same coefficient, the same items where it is not
0, and the same bases in `N` of the factors and the ones are equal. -/
public theorem finish_eq {o : Orders} (ho : o.Total) {p q : ProductParts}
    (hc : p.coefficient = q.coefficient) (hi : p.coefficient ≠ 0 → p.items = q.items)
    (hN : ∀ b, b ∈ Term.negBasesList (p.items.map itemFactor ++ p.ones) ↔
      b ∈ Term.negBasesList (q.items.map itemFactor ++ q.ones)) : finish o p = finish o q := by
  obtain ⟨c, its, os⟩ := p; obtain ⟨c', its', os'⟩ := q
  dsimp only at hc hi hN; subst hc
  by_cases h0 : c = 0
  · unfold finish; dsimp only; rw [ite_eq_left h0, ite_eq_left h0,
      maxBases_congr (termCmp_total o ho) hN]
  · obtain rfl := hi h0
    exact finish_congr (termCmp_total o ho) fun b => by
      have := hN b; rw [mem_negBasesList_append, mem_negBasesList_append] at this; tauto

end Kalyx.Proofs.Terms.Products
