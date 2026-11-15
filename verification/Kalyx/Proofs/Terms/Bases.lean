module

public import Kalyx.Statements.Terms
public import Kalyx.Proofs.Terms.Basics
public import Kalyx.Proofs.Terms.Order
public import Kalyx.Proofs.Terms.Sums

/-!
# The bases of negative powers, and calls as atoms

Proves `CallsAreAtoms`, and `ConstructorsKeepNegativeBases` given `NegationReadsOpposite`. Every
stage of a sum, a product and a power keeps `N` exactly and builds only numbers, powers, products
and sums over nodes of its operands (`NodesFrom`); a power of a canonical base merges at most
once. So each constructor returns exactly the bases of its operands and those that a negative
power introduces, and only calls of its operands. The parts of the operands of a product and its
rounds keep `N` (`productParts_negBases`, `settleItems_negBases`); the merging of products uses
that, and the cases of a power (`mkPower_cases`) are shared.
-/

namespace Kalyx.Proofs.Terms.Bases

open Kalyx.Spec.Terms Kalyx.Statements.Terms Kalyx.Proofs.Terms

/-! ## `N` of powers and witnesses -/

/-- `N` of a power: its base for a negative exponent over a base that is not a constant. -/
private theorem mem_negBases_power {b x : Term} {k : ℤ} :
    x ∈ (Term.power b k).negBases ↔ (k < 0 ∧ b.isConstant = false ∧ x = b) ∨ x ∈ b.negBases := by
  simp [Term.negBases, and_assoc]

/-- `N` of a power depends only on the key of its item. -/
private theorem negBases_power_key {b c : Term} {j k : ℤ} (h : Key.of b j = Key.of c k) :
    (Term.power b j).negBases = (Term.power c k).negBases := by
  simp only [Key.of, Key.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  cases hb : b.isConstant <;> simp_all [Term.negBases]

/-- `N` of a one is `N` of the reciprocal of its base. -/
private theorem negBases_oneOf (b : Term) : b.oneOf.negBases = b.reciprocal.negBases := by
  simp [Term.oneOf, Term.reciprocal, Term.negBases]

/-- The reciprocals of the maximal elements of bases hold exactly the bases and their `N`. -/
private theorem negBases_maxRecips (o : Orders) {L : List Term}
    (hc : ∀ b ∈ L, b.isConstant = false) {x : Term} :
    x ∈ Term.negBasesList ((maxBases o L).map Term.reciprocal) ↔
      x ∈ L ∨ ∃ b ∈ L, x ∈ b.negBases := by
  rw [mem_negBases_reciprocals fun b hb => hc b (maxBases_subset hb)]
  refine ⟨fun ⟨b, hb, h⟩ => h.elim (fun h => .inl (h ▸ maxBases_subset hb))
    fun h => .inr ⟨b, maxBases_subset hb, h⟩, ?_⟩
  rintro (hx | ⟨b, hb, hx⟩)
  · rcases maxBases_cover o L hx with h | ⟨m, hm, h⟩
    exacts [⟨x, h, .inl rfl⟩, ⟨m, hm, .inr h⟩]
  · rcases maxBases_cover o L hb with h | ⟨m, hm, h⟩
    exacts [⟨b, h, .inr hx⟩, ⟨m, hm, .inr (negBases_trans h hx)⟩]

/-- `N` of a list of terms holds `N` of its bases, which are no constants. -/
private theorem negBasesList_closed {ts : List Term} {b : Term} (hb : b ∈ Term.negBasesList ts) :
    b.isConstant = false ∧ ∀ x ∈ b.negBases, x ∈ Term.negBasesList ts :=
  let ⟨t, ht, hb⟩ := mem_negBasesList.1 hb
  ⟨negBases_isConstant hb, fun _ hx => mem_negBasesList.2 ⟨t, ht, negBases_trans hb hx⟩⟩

/-- `N` of the zero witness, of the witness core and of the power 0. -/
private theorem negBases_witnesses (o : Orders) (bs : List Term) (t x : Term) :
    (x ∈ (zeroWitness bs).negBases ↔ x ∈ Term.negBasesList (bs.map Term.reciprocal)) ∧
    (x ∈ (witnessCore bs).negBases ↔ x ∈ Term.negBasesList (bs.map Term.reciprocal)) ∧
    (x ∈ (powerZero o t).negBases ↔ x ∈ t.negBases) := by
  refine ⟨by cases bs <;> simp [zeroWitness, Term.negBases, Term.negBasesList], ?_, ?_⟩
  · match bs with
    | [b] => simp [witnessCore, Term.negBasesList]
    | [] | _ :: _ :: _ => simp [witnessCore, Term.negBases]
  · have e : x ∈ (powerZero o t).negBases ↔
        x ∈ Term.negBasesList ((maxBases o t.negBases).map Term.reciprocal) := by
      unfold powerZero; split <;> rename_i heq <;>
        simp [heq, Term.negBases, Term.negBasesList, negBases_oneOf, mem_negBasesList]
    rw [e, negBases_maxRecips o fun b hb => negBases_isConstant hb]
    exact ⟨fun h => h.elim id fun ⟨b, hb, hx⟩ => negBases_trans hb hx, .inl⟩

/-- A product of the images of terms is built from `ts` when the images are. -/
private theorem nodesFrom_map {ts bs : List Term} {f : Term → Term} (c : ℚ)
    (h : ∀ b ∈ bs, NodesFrom ts (f b)) : NodesFrom ts (.product c (bs.map f)) :=
  NodesFrom.product c fun g hg => by obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hg; exact h b hb

/-- The zero witness and the witness core of bases built from `ts` are built from `ts`. -/
private theorem nodesFrom_witnesses {ts bs : List Term} (h : ∀ b ∈ bs, NodesFrom ts b) :
    NodesFrom ts (zeroWitness bs) ∧ NodesFrom ts (witnessCore bs) := by
  have hr := fun c => nodesFrom_map (f := Term.reciprocal) c fun b hb => (h b hb).power (-1)
  refine ⟨by unfold zeroWitness; split; exacts [.number 0, hr 0], ?_⟩
  match bs, h with
  | [b], h => exact (h b (by simp)).power _
  | [], _ | _ :: _ :: _, _ => exact hr 1

/-- The power 0 of a term is built from it. -/
private theorem nodesFrom_powerZero (o : Orders) (t : Term) : NodesFrom [t] (powerZero o t) := by
  have h : ∀ b ∈ maxBases o t.negBases, NodesFrom [t] b := fun b hb =>
    .of_mem (List.mem_singleton_self t) (negBases_mem_nodes (maxBases_subset hb))
  unfold powerZero; split <;> rename_i heq
  · exact .number 1
  · exact ((h _ (by simp [heq])).power _).power _
  · exact nodesFrom_map 1 fun b hb => ((h b hb).power _).power _

/-- A scaled sum has `N` of the sum, and is built from it. -/
private theorem scaleSum_bases (a c : ℚ) (ms : List (ℚ × Term)) :
    (scaleSum a c ms).negBases = (Term.sum c ms).negBases ∧
      NodesFrom [.sum c ms] (scaleSum a c ms) := by
  refine ⟨?_, NodesFrom.sum _ fun m hm => ?_⟩
  · simp only [scaleSum, Term.negBases]
    induction ms with
    | nil => rfl
    | cons m ms ih => obtain ⟨q, t⟩ := m; simp [Term.negBasesPairs, ih]
  · obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hm
    exact .of_mem (List.mem_singleton_self _)
      (by simp only [Term.nodes]; exact .tail _ (mem_nodesPairs.2 ⟨n, hn, mem_nodes_self _⟩))

/-- `N` of two lists of terms together. -/
@[simp] private theorem negBasesList_append (ts ts' : List Term) :
    Term.negBasesList (ts ++ ts') = Term.negBasesList ts ++ Term.negBasesList ts' := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [Term.negBasesList, ih]

/-! ## Sums -/

/-- The monomials that a sum reads from its operands have their `N`, and cores built from them. -/
private theorem sumParts_bases : ∀ ts : List Term,
    (∀ b, b ∈ Term.negBasesPairs (sumParts ts).2 ↔ b ∈ Term.negBasesList ts) ∧
      ∀ m ∈ (sumParts ts).2, NodesFrom ts m.2
  | [] => by simp [sumParts, Term.negBasesPairs, Term.negBasesList]
  | t :: ts => by
    have h : (∀ b, b ∈ Term.negBasesPairs (sumParts [t]).2 ↔ b ∈ t.negBases) ∧
        ∀ m ∈ (sumParts [t]).2, NodesFrom [t] m.2 := by
      have hs : ∀ {x}, x ∈ t.nodes → NodesFrom [t] x := .of_mem (List.mem_singleton_self t)
      cases t with
      | number q => simp [sumParts, Term.negBasesPairs, Term.negBases]
      | sum c ms =>
        simp only [sumParts, List.append_nil]
        exact ⟨fun b => by simp [Term.negBases], fun m hm =>
          hs (by simp only [Term.nodes]; exact .tail _ (mem_nodesPairs.2 ⟨m, hm, mem_nodes_self _⟩))⟩
      | product c fs =>
        have hf : ∀ f ∈ fs, NodesFrom [.product c fs] f := fun f hf => hs (mem_nodes_factor hf)
        match fs, hf with
        | [f], hf => simp [sumParts, productCore, Term.negBasesPairs, Term.negBases,
            Term.negBasesList, hf f (by simp)]
        | [], hf | _ :: _ :: _, hf => simp [sumParts, productCore, Term.negBasesPairs,
            Term.negBases, NodesFrom.product 1 hf]
      | _ => simp [sumParts, Term.negBasesPairs, hs (mem_nodes_self _)]
    obtain ⟨ih1, ih2⟩ := sumParts_bases ts; rw [Sums.sumParts_cons]
    refine ⟨fun b => ?_, fun m hm => (List.mem_append.1 hm).elim (fun hm => (h.2 m hm).mono
      (by simp)) fun hm => (ih2 m hm).mono fun _ => List.mem_cons_of_mem _⟩
    rw [Term.negBasesList, List.mem_append, ← h.1, ← ih1]
    simp only [mem_negBasesPairs, List.mem_append, or_and_right, exists_or]

/-- Merging monomials keeps their cores, so their `N`. -/
private theorem mergeMonomials_bases (o : Orders) (ms : List (ℚ × Term)) :
    (∀ b, b ∈ Term.negBasesPairs (mergeMonomials o ms) ↔ b ∈ Term.negBasesPairs ms) ∧
      ∀ m ∈ mergeMonomials o ms, ∃ a ∈ ms, a.2 = m.2 := by
  have hj : ∀ x y z : ℚ × Term, (if x.2 = y.2 then some (x.1 + y.1, x.2) else none) = some z →
      x.2 = z.2 ∧ y.2 = z.2 := fun x y z h => by split at h <;> cases h; simp_all
  have hp := perm_sortBy (monomialCmp o) ms
  have hf : ∀ m ∈ mergeMonomials o ms, ∃ a ∈ ms, a.2 = m.2 := fun m hm =>
    let ⟨a, ha, e⟩ := mergeAdjacent_from _ Prod.snd hj _ m hm; ⟨a, hp.mem_iff.1 ha, e⟩
  refine ⟨fun b => ⟨fun hb => ?_, fun hb => ?_⟩, hf⟩ <;> obtain ⟨m, hm, hb⟩ := mem_negBasesPairs.1 hb
  · obtain ⟨a, ha, e⟩ := hf m hm; exact mem_negBasesPairs.2 ⟨a, ha, e ▸ hb⟩
  · obtain ⟨a, ha, e⟩ := mergeAdjacent_cover _ Prod.snd hj _ m (hp.mem_iff.2 hm)
    exact mem_negBasesPairs.2 ⟨a, ha, e ▸ hb⟩

/-- Cancellation keeps `N` of the monomials, and builds its cores from theirs. -/
private theorem cancelMonomials_bases (o : Orders) (ms : List (ℚ × Term)) :
    (∀ b, b ∈ Term.negBasesPairs (cancelMonomials o ms) ↔ b ∈ Term.negBasesPairs ms) ∧
      ∀ {ts : List Term}, (∀ m ∈ ms, NodesFrom ts m.2) →
        ∀ m ∈ cancelMonomials o ms, NodesFrom ts m.2 := by
  unfold cancelMonomials; dsimp only
  generalize hR : ms.filter (fun m => decide (m.1 ≠ 0)) = R
  generalize hL : uncovered (Term.negBasesPairs (ms.filter fun m => decide (m.1 = 0)))
    (Term.negBasesPairs R) = L
  have hRm : ∀ m ∈ R, m ∈ ms := fun m hm => (List.mem_filter.1 (hR ▸ hm)).1
  have hLN : ∀ x, x ∈ L ↔ (∃ m ∈ ms, m.1 = 0 ∧ x ∈ m.2.negBases) ∧ x ∉ Term.negBasesPairs R := by
    intro x; subst hL; simp [uncovered, mem_negBasesPairs, and_assoc]
  have hW : ∀ x, x ∈ Term.negBasesList ((maxBases o L).map Term.reciprocal) ↔
      (x ∈ Term.negBasesPairs ms ∧ x ∉ Term.negBasesPairs R) ∨
        ∃ b ∈ L, x ∈ b.negBases := fun x => by
    refine (negBases_maxRecips o fun b hb => ?_).trans (or_congr_left ?_)
    · obtain ⟨⟨m, -, -, hb⟩, -⟩ := (hLN b).1 hb; exact negBases_isConstant hb
    rw [hLN]; constructor
    · rintro ⟨⟨m, hm, -, h⟩, h'⟩; exact ⟨mem_negBasesPairs.2 ⟨m, hm, h⟩, h'⟩
    · rintro ⟨h, h'⟩
      obtain ⟨m, hm, h⟩ := mem_negBasesPairs.1 h
      refine ⟨⟨m, hm, ?_, h⟩, h'⟩
      by_contra h0
      exact h' (mem_negBasesPairs.2 ⟨m, hR ▸ List.mem_filter.2 ⟨hm, by simpa using h0⟩, h⟩)
  have key : ∀ b, b ∈ Term.negBasesPairs R ∨ b ∈ Term.negBasesList ((maxBases o L).map
      Term.reciprocal) ↔ b ∈ Term.negBasesPairs ms := fun b => by
    rw [hW]; refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with h | ⟨h, -⟩ | ⟨c, hc, hb⟩
      · obtain ⟨m, hm, h⟩ := mem_negBasesPairs.1 h; exact mem_negBasesPairs.2 ⟨m, hRm m hm, h⟩
      · exact h
      · obtain ⟨⟨m, hm, -, hc⟩, -⟩ := (hLN c).1 hc
        exact mem_negBasesPairs.2 ⟨m, hm, negBases_trans hc hb⟩
    · by_cases hb : b ∈ Term.negBasesPairs R; exacts [.inl hb, .inr (.inl ⟨h, hb⟩)]
  have hWn : ∀ {ts : List Term}, (∀ m ∈ ms, NodesFrom ts m.2) → ∀ b ∈ maxBases o L,
      NodesFrom ts b := fun hn b hb => by
    obtain ⟨⟨m, hm, -, hb⟩, -⟩ := (hLN b).1 (maxBases_subset hb); exact (hn m hm).sub (negBases_mem_nodes hb)
  split <;> rename_i heq
  · exact ⟨fun b => by simpa [heq, Term.negBasesList] using key b, fun hn m hm => hn m (hRm m hm)⟩
  · have hp := perm_insertBy (monomialCmp o) (0, witnessCore (maxBases o L)) R
    refine ⟨fun b => ?_, fun hn m hm => ?_⟩
    · have e : b ∈ Term.negBasesPairs (insertBy (monomialCmp o) (0, witnessCore (maxBases o L)) R)
          ↔ b ∈ Term.negBasesPairs R ∨ b ∈ (witnessCore (maxBases o L)).negBases := by
        simp [mem_negBasesPairs, hp.mem_iff, or_comm]
      rw [e, (negBases_witnesses o _ (.number 0) b).2.1, key]
    · rcases List.mem_cons.1 (hp.mem_iff.1 hm) with rfl | hm
      exacts [(nodesFrom_witnesses (hWn hn)).2, hn m (hRm m hm)]

/-- The assembly of a sum keeps `N` of its monomials, and is built from their cores. -/
private theorem assembleSum_bases (c : ℚ) (ms : List (ℚ × Term)) :
    (∀ b, b ∈ (assembleSum c ms).negBases ↔ b ∈ Term.negBasesPairs ms) ∧
      ∀ {ts : List Term}, (∀ m ∈ ms, NodesFrom ts m.2) → NodesFrom ts (assembleSum c ms) := by
  match ms with
  | [] => exact ⟨by simp [assembleSum, Term.negBases, Term.negBasesPairs], fun _ => .number c⟩
  | [(a, t)] =>
    by_cases hc : c = 0 <;> by_cases ha : a = 1 <;>
      simp only [assembleSum, hc, ha, ite_true, ite_false, List.mem_singleton, forall_eq]
    · simp [Term.negBasesPairs]
    · refine ⟨fun b => ?_, fun h => NodesFrom.product _ fun f hf' => h.sub (coreFactors_nodes hf')⟩
      cases t <;> simp [Term.coreFactors, Term.negBases, Term.negBasesList, Term.negBasesPairs]
    all_goals exact ⟨by simp [Term.negBases], fun h => NodesFrom.sum c (by simpa using h)⟩
  | _ :: _ :: _ => exact ⟨fun b => by simp [assembleSum, Term.negBases], fun h => .sum c h⟩

/-- A sum: `N` of the result is `N` of the operands, and its nodes are built or of an operand. -/
public theorem mkSum_bases {o : Orders} {ts : List Term} {u : Term} (h : mkSum o ts = .value u) :
    (∀ b, b ∈ u.negBases ↔ b ∈ Term.negBasesList ts) ∧ NodesFrom ts u := by
  unfold mkSum at h; split at h <;> cases h
  obtain ⟨hp1, hp2⟩ := sumParts_bases ts
  obtain ⟨hm1, hm2⟩ := mergeMonomials_bases o (sumParts ts).2
  obtain ⟨hc1, hc2⟩ := cancelMonomials_bases o (mergeMonomials o (sumParts ts).2)
  obtain ⟨ha1, ha2⟩ := assembleSum_bases (sumParts ts).1 (cancelMonomials o (mergeMonomials o _))
  exact ⟨fun b => (ha1 b).trans ((hc1 b).trans ((hm1 b).trans (hp1 b))),
    ha2 (hc2 fun m hm => let ⟨a, ha, e⟩ := hm2 m hm; e ▸ hp2 a ha)⟩

/-! ## Products -/

/-- Parts `p` stand for `ts`: the same `N`, exponents other than 0, terms built from `ts`. -/
private def PartsOf (ts : List Term) (p : ProductParts) : Prop :=
  (∀ b, b ∈ Term.negBasesList (partsTerms p) ↔ b ∈ Term.negBasesList ts) ∧
    (∀ x ∈ p.items, x.2 ≠ 0) ∧ ∀ s ∈ partsTerms p, NodesFrom ts s

/-- Parts of `ts` stand for `ts'` when `ts` has the `N` of `ts'` and is built from it. -/
private theorem partsOf_trans {ts ts' : List Term} {p : ProductParts} (h : PartsOf ts p)
    (hN : ∀ b, b ∈ Term.negBasesList ts ↔ b ∈ Term.negBasesList ts')
    (hn : ∀ t ∈ ts, NodesFrom ts' t) : PartsOf ts' p :=
  ⟨fun b => (h.1 b).trans (hN b), h.2.1, fun s hs => (h.2.2 s hs).trans' hn⟩

/-- One item `(X, q)` stands for `t` when its power has `N(t)` and `X` is built from `t`. -/
private theorem partsOf_item {t X : Term} {q : ℤ} (c : ℚ) (hq : q ≠ 0)
    (hN : ∀ x, x ∈ (Term.power X q).negBases ↔ x ∈ t.negBases) (hn : NodesFrom [t] X) :
    PartsOf [t] ⟨c, [(X, q)], []⟩ :=
  ⟨fun x => by simpa [partsTerms, Term.negBasesList] using hN x, by simpa,
    by simpa [partsTerms] using hn.power q⟩

/-- Parts made of `base` and of parts `view r` for `g x` (`f x = r`) stand for `base`, `g x`. -/
private theorem partsOf_union {γ δ : Type} {f : γ → Result δ} {g : γ → Term}
    {view : δ → ProductParts} {xs : List γ} {rs : List δ} (hm : xs.mapM f = .value rs)
    (hf : ∀ x ∈ xs, ∀ r, f x = .value r → PartsOf [g x] (view r)) {base : List Term}
    {p : ProductParts} (hs : ∀ s, s ∈ partsTerms p ↔ s ∈ base ∨ ∃ r ∈ rs, s ∈ partsTerms (view r))
    (hi : ∀ y ∈ p.items, ∃ r ∈ rs, y ∈ (view r).items) : PartsOf (base ++ xs.map g) p := by
  obtain ⟨hl, hr⟩ := mapM_mem hm
  have hv : ∀ r ∈ rs, ∃ x ∈ xs, PartsOf [g x] (view r) := fun r hr' =>
    let ⟨x, hx, h⟩ := hr r hr'; ⟨x, hx, hf x hx r h⟩
  refine ⟨fun b => ?_, fun y hy => ?_, fun s hs' => ?_⟩
  · simp only [mem_negBasesList, hs, List.mem_append, List.mem_map, or_and_right, exists_or]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨s, ⟨r, hr', hs⟩, hb⟩
      obtain ⟨x, hx, hP⟩ := hv r hr'
      obtain ⟨t, ht, hb⟩ := mem_negBasesList.1 ((hP.1 b).1 (mem_negBasesList.2 ⟨s, hs, hb⟩))
      exact ⟨t, ⟨x, hx, (List.mem_singleton.1 ht).symm⟩, hb⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, hb⟩
      obtain ⟨r, hr', hfx⟩ := hl x hx
      obtain ⟨s, hs, hb⟩ := mem_negBasesList.1
        (((hf x hx r hfx).1 b).2 (mem_negBasesList.2 ⟨_, List.mem_singleton_self _, hb⟩))
      exact ⟨s, ⟨r, hr', hs⟩, hb⟩
  · obtain ⟨r, hr', hy⟩ := hi y hy
    exact (hv r hr').choose_spec.2.2.1 y hy
  · rcases (hs s).1 hs' with hs' | ⟨r, hr', hs'⟩
    · exact .self (List.mem_append_left _ hs')
    · obtain ⟨x, hx, hP⟩ := hv r hr'
      exact (hP.2.2 s hs').mono fun t ht =>
        List.mem_append_right _ (List.mem_map.2 ⟨x, hx, (List.mem_singleton.1 ht).symm⟩)

/-- The parts of a power `t ^ q`, `q ≥ 1`, of an item stand for `t`. -/
private theorem itemParts_bases {me : ℕ} {q : ℤ} (hq : 1 ≤ q) {t : Term} {p : ProductParts}
    (h : itemParts me q t = .value p) : PartsOf [t] p := by
  have hs : ∀ {x}, x ∈ t.nodes → NodesFrom [t] x := .of_mem (List.mem_singleton_self t)
  have hpos : ∀ b : Term, (Term.power b q).negBases = b.negBases := fun b =>
    negBases_power_pos (by omega)
  cases t with
  | sum c ms =>
    simp only [itemParts, Result.value.injEq] at h; subst h
    exact partsOf_item _ (by omega) (fun x => by simp [hpos, primitivePart, (scaleSum_bases _ c ms).1])
      (scaleSum_bases _ c ms).2
  | power b j =>
    simp only [itemParts] at h; split at h
    · simp only [Result.value.injEq] at h; subst h
      exact ⟨by simp [partsTerms, Term.negBasesList], by simp, by simp [partsTerms, hs, mem_nodes_self]⟩
    · unfold checkExponent at h; split at h; · cases h
      simp only [Result.value.injEq] at h; subst h
      refine partsOf_item _ (by simp_all; omega) (fun x => ?_) (hs (by simp [Term.nodes, mem_nodes_self]))
      simp only [Term.negBases, show j * q < 0 ↔ j < 0 from ⟨fun h => by nlinarith, fun h => by nlinarith⟩]
  | _ =>
    simp only [itemParts, Result.value.injEq] at h; subst h
    exact partsOf_item _ (by omega) (fun x => by rw [hpos]) (hs (mem_nodes_self _))

/-- The parts of a power `t ^ q`, `q ≥ 1`, of a term stand for `t`. -/
private theorem factorParts_bases {me : ℕ} {q : ℤ} (hq : 1 ≤ q) {t : Term} {p : ProductParts}
    (h : factorParts me q t = .value p) : PartsOf [t] p := by
  cases t with
  | number r =>
    simp only [factorParts, Result.value.injEq] at h; subst h
    exact ⟨by simp [partsTerms, Term.negBasesList, Term.negBases], by simp, by simp [partsTerms]⟩
  | product c fs =>
    obtain ⟨ps, hps, h⟩ := bind_eq_value.1 h; simp only [pure_value, Result.value.injEq] at h; subst h
    have := partsOf_union (base := []) (g := id) (view := id)
      (p := ps.foldl ProductParts.append ⟨c ^ q, [], []⟩) hps (fun x _ r h => itemParts_bases hq h)
      (fun s => by rw [mem_partsTerms_foldl]; simp [partsTerms])
      (fun y hy => by simpa using (mem_items_foldl ps _).1 hy)
    exact partsOf_trans (by simpa using this) (fun b => by simp [Term.negBasesList, Term.negBases])
      fun f hf => .of_mem (List.mem_singleton_self _) (mem_nodes_factor hf)
  | _ => exact itemParts_bases hq (by simpa [factorParts] using h)

/-- The parts of the operands of a product stand for them. -/
private theorem productParts_bases {me : ℕ} {ts : List Term} {p : ProductParts}
    (h : productParts me ts = .value p) : PartsOf ts p := by
  obtain ⟨ps, hps, h⟩ := bind_eq_value.1 h; simp only [pure_value, Result.value.injEq] at h; subst h
  simpa using partsOf_union (base := []) (g := id) (view := id)
    (p := ps.foldl ProductParts.append ProductParts.unit) hps
    (fun x _ r h => factorParts_bases le_rfl h)
    (fun s => by rw [mem_partsTerms_foldl]; simp [partsTerms, ProductParts.unit])
    (fun y hy => by simpa [ProductParts.unit] using (mem_items_foldl ps _).1 hy)

/-- The parts of the operands of a product: exponents other than 0, and `N` of the operands. -/
public theorem productParts_negBases {me : ℕ} {ts : List Term} {p : ProductParts}
    (h : productParts me ts = .value p) : (∀ x ∈ p.items, x.2 ≠ 0) ∧
      ∀ b, b ∈ Term.negBasesList (partsTerms p) ↔ b ∈ Term.negBasesList ts :=
  ⟨(productParts_bases h).2.1, (productParts_bases h).1⟩

/-- Merging items keeps `N` of their powers and their bases; exponents 0 only over constants. -/
private theorem mergeItems_bases (o : Orders) (items : List (Term × ℤ))
    (hn : ∀ x ∈ items, x.2 ≠ 0) :
    (∀ b, b ∈ Term.negBasesList ((mergeItems o items).map fun y => Term.power y.1 y.2) ↔
      b ∈ Term.negBasesList (items.map fun y => Term.power y.1 y.2)) ∧
    ∀ y ∈ mergeItems o items, (y.2 ≠ 0 ∨ y.1.isConstant = true) ∧ ∃ x ∈ items, x.1 = y.1 := by
  have hj : ∀ x y z : Term × ℤ,
      (if Key.of x.1 x.2 = Key.of y.1 y.2 then some (x.1, x.2 + y.2) else none) = some z →
        Key.of x.1 x.2 = Key.of z.1 z.2 ∧ Key.of y.1 y.2 = Key.of z.1 z.2 := fun x y z h => by
    split at h <;> cases h; rename_i e; exact ⟨(key_add e).symm, e.symm.trans (key_add e).symm⟩
  have hp := perm_sortBy (fun x y : Term × ℤ => Key.cmp o (Key.of x.1 x.2) (Key.of y.1 y.2)) items
  have hf := mergeAdjacent_from _ (fun x : Term × ℤ => Key.of x.1 x.2) hj
  have hc := mergeAdjacent_cover _ (fun x : Term × ℤ => Key.of x.1 x.2) hj
  unfold mergeItems
  refine ⟨fun b => ?_, fun y hy => ⟨mergeAdjacent_forall _
    (fun y : Term × ℤ => y.2 ≠ 0 ∨ y.1.isConstant = true) ?_ _
    (fun a ha => .inl (hn a (hp.mem_iff.1 ha))) y hy,
    let ⟨x, hx, e⟩ := hf _ y hy; ⟨x, hp.mem_iff.1 hx, congrArg Key.base e⟩⟩⟩
  · simp only [mem_negBasesList, List.mem_map]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, hb⟩
      obtain ⟨x, hx, e⟩ := hf _ y hy
      exact ⟨_, ⟨x, hp.mem_iff.1 hx, rfl⟩, negBases_power_key e ▸ hb⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, hb⟩
      obtain ⟨y, hy, e⟩ := hc _ x (hp.mem_iff.2 hx)
      exact ⟨_, ⟨y, hy, rfl⟩, negBases_power_key e ▸ hb⟩
  · intro x y z hz hx hy
    split at hz <;> cases hz
    rename_i e
    simp only [Key.of, Key.mk.injEq] at e
    obtain ⟨e1, e2⟩ := e
    cases hb : x.1.isConstant
    · rw [e1] at hb; simp_all; omega
    · exact .inr rfl

/-- The parts that the reduction of an item returns, all together, stand for its power. -/
private theorem reduceItem_bases {me : ℕ} {x : Term × ℤ} {r : ProductParts × List (Term × ℤ)}
    (hx : x.2 ≠ 0 ∨ x.1.isConstant = true) (h : reduceItem me x = .value r) :
    PartsOf [Term.power x.1 x.2] ⟨r.1.coefficient, r.1.items ++ r.2, r.1.ones⟩ := by
  obtain ⟨b, k⟩ := x
  have hs : ∀ {y}, y ∈ (Term.power b k).nodes → NodesFrom [Term.power b k] y :=
    .of_mem (List.mem_singleton_self _)
  have hb : NodesFrom [Term.power b k] b := hs (by simp [Term.nodes, mem_nodes_self])
  have one : k ≠ 0 → PartsOf [Term.power b k] ⟨1, [(b, k)] ++ [], []⟩ := fun hk => by
    simpa using partsOf_item 1 hk (fun x => Iff.rfl) hb
  simp only [reduceItem, checkExponent] at h; split at h; · cases h
  split at h
  · cases h; rename_i hk
    have hc : b.isConstant = true := hx.resolve_left (by simpa using hk)
    refine ⟨fun _ => ?_, by simp [ProductParts.unit], by simp [partsTerms, ProductParts.unit]⟩
    cases b <;> simp_all [partsTerms, ProductParts.unit, Term.negBasesList, Term.negBases,
      Term.isConstant]
  rename_i hk; split at h
  · cases h; rename_i hi; subst hi
    refine ⟨fun x => ?_, fun y hy => ?_, fun s hs' => ?_⟩
    · split_ifs <;> simp [partsTerms, Term.negBasesList, Term.negBases, Term.imaginaryUnit,
        Term.isConstant]
    · split_ifs at hy <;> simp_all
    · split_ifs at hs' <;> simp_all [partsTerms] <;> exact hb.power 1
  cases hr : rootOf b with
  | none => simp only [hr, Result.value.injEq] at h; subst h; exact one hk
  | some un =>
    obtain ⟨u, n⟩ := un
    obtain ⟨hn, hd, rest, hbe, hrest⟩ := rootOf_some hr
    have hu : u ∈ b.nodes := by simp [hbe, Term.nodes, mem_nodesList, mem_nodes_self]
    have hN : ∀ x, x ∈ b.negBases ↔ x ∈ u.negBases := fun x => by
      simp only [hbe, Term.negBases, Term.negBasesList, List.mem_append, or_iff_left_iff_imp]
      intro hx; obtain ⟨a, ha, hx⟩ := mem_negBasesList.1 hx; obtain ⟨q, rfl⟩ := hrest a ha
      simp [Term.negBases] at hx
    simp only [hr] at h
    split at h
    · rename_i hnk
      obtain ⟨p, hp, h⟩ := bind_eq_value.1 h
      simp only [pure_value, Result.value.injEq] at h; subst h
      obtain ⟨hP1, hP2, hP3⟩ := factorParts_bases (Int.le_ediv_of_mul_le (by omega)
        (by simpa using hnk)) hp
      have hkn : 0 ≤ k % n := Int.emod_nonneg _ (by omega)
      have gen : ∀ L : List (Term × ℤ), (∀ y ∈ L, y.1 = b ∧ 0 < y.2) →
          PartsOf [Term.power b k] ⟨p.coefficient, L ++ p.items, p.ones⟩ := fun L hL => by
        have e : partsTerms ⟨p.coefficient, L ++ p.items, p.ones⟩ =
            L.map (fun y => Term.power y.1 y.2) ++ partsTerms p := by simp [partsTerms]
        refine ⟨fun x => ?_, fun y hy => ?_, fun s hs' => ?_⟩
        · rw [e, negBasesList_append, List.mem_append, hP1]
          simp only [Term.negBasesList, List.append_nil, negBases_power_pos (show 0 ≤ k by omega),
            ← hN]
          refine ⟨fun h => h.elim (fun h => ?_) id, .inr⟩
          obtain ⟨t, ht, hx⟩ := mem_negBasesList.1 h
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ht
          rwa [(hL y hy).1, negBases_power_pos (hL y hy).2.le] at hx
        · exact (List.mem_append.1 hy).elim (fun hy => (hL y hy).2.ne') (hP2 y)
        · rw [e] at hs'
          rcases List.mem_append.1 hs' with hs' | hs'
          · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hs'; rw [(hL y hy).1]; exact hb.power _
          · exact (hP3 s hs').trans' fun t ht => by
              rw [List.mem_singleton.1 ht]
              exact hs (by simp only [Term.nodes]; exact .tail _ (nodes_trans hu (mem_nodes_self u)))
      split_ifs
      · exact gen [] (by simp)
      · exact gen [(b, k % n)] (by simp; omega)
    · simp only [Result.value.injEq] at h; subst h; exact one hk

/-- A round of merging and reduction: its next state stands for the parts before it. -/
private theorem round_bases {o : Orders} {me : ℕ} {p : ProductParts}
    {rs : List (ProductParts × List (Term × ℤ))} (hn : ∀ x ∈ p.items, x.2 ≠ 0)
    (hrs : (mergeItems o p.items).mapM (reduceItem me) = .value rs) :
    PartsOf (partsTerms p) ⟨p.coefficient * (rs.map fun r => r.1.coefficient).prod,
      (rs.map fun r => r.1.items).flatten ++ (rs.map Prod.snd).flatten,
      p.ones ++ (rs.map fun r => r.1.ones).flatten⟩ := by
  obtain ⟨hm1, hm2⟩ := mergeItems_bases o p.items hn
  refine partsOf_trans (partsOf_union (g := fun x : Term × ℤ => Term.power x.1 x.2)
    (base := p.ones) (view := fun r : ProductParts × List (Term × ℤ) =>
      ⟨r.1.coefficient, r.1.items ++ r.2, r.1.ones⟩)
    hrs (fun x hx r h => reduceItem_bases (hm2 x hx).1 h) (fun s => ?_) (fun y hy => ?_))
    (fun b => ?_) (fun t ht => ?_)
  · simp only [partsTerms, List.mem_append, List.mem_map, List.mem_flatten]; aesop
  · simp only [List.mem_append, List.mem_flatten, List.mem_map] at hy; aesop
  · simp only [partsTerms, negBasesList_append, List.mem_append, hm1, or_comm]
  · rcases List.mem_append.1 ht with ht | ht
    · exact .self (List.mem_append_right _ ht)
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ht
      obtain ⟨x, hx, e⟩ := (hm2 y hy).2
      exact .power _ (.of_mem (List.mem_append_left _ (List.mem_map.2 ⟨x, hx, rfl⟩))
        (by simp [Term.nodes, e, mem_nodes_self]))

/-- The rounds of merging and reduction keep `N` of the parts and build their terms from them. -/
private theorem settleItems_bases {o : Orders} {me : ℕ} : ∀ (fuel : ℕ) (p p' : ProductParts),
    settleItems o me fuel p = .value p' → (∀ x ∈ p.items, x.2 ≠ 0) → PartsOf (partsTerms p) p'
  | 0, _, _, h, _ => by simp [settleItems] at h
  | fuel + 1, p, p', h, hn => by
    rw [settleItems] at h; obtain ⟨rs, hrs, h⟩ := bind_eq_value.1 h
    have hR := round_bases hn hrs
    have hfold := foldl_append (rs.map Prod.fst) ⟨p.coefficient, [], p.ones⟩; rw [List.foldl_map] at hfold
    simp only [hfold, List.nil_append, List.map_map, Function.comp_def] at h
    split at h
    · simp only [pure_value, Result.value.injEq] at h; subst h
      simpa [List.isEmpty_iff.1 ‹_›] using hR
    · exact partsOf_trans (settleItems_bases fuel _ _ h hR.2.1) hR.1 hR.2.2

/-- The rounds keep `N` of the terms of parts whose exponents are not 0. -/
public theorem settleItems_negBases {o : Orders} {me fuel : ℕ} {p p' : ProductParts}
    (h : settleItems o me fuel p = .value p') (hn : ∀ x ∈ p.items, x.2 ≠ 0) (b : Term) :
    b ∈ Term.negBasesList (partsTerms p') ↔ b ∈ Term.negBasesList (partsTerms p) :=
  (settleItems_bases fuel p p' h hn).1 b

/-- The assembly of a product keeps `N` of its factors, and is built from them. -/
private theorem assembleProduct_bases (c : ℚ) (fs : List Term) :
    (∀ b, b ∈ (assembleProduct c fs).negBases ↔ b ∈ Term.negBasesList fs) ∧
      ∀ {ts : List Term}, (∀ f ∈ fs, NodesFrom ts f) → NodesFrom ts (assembleProduct c fs) := by
  match fs with
  | [] => exact ⟨by simp [assembleProduct, Term.negBases, Term.negBasesList], fun _ => .number c⟩
  | [f] =>
    by_cases h1 : c = 1
    · simp only [assembleProduct, h1, ite_true]
      exact ⟨by simp [Term.negBasesList], fun h => h f (by simp)⟩
    cases f with
    | sum a ms =>
      simp only [assembleProduct, h1, ite_false]
      exact ⟨by simp [Term.negBasesList, (scaleSum_bases _ _ _).1],
        fun h => (scaleSum_bases c a ms).2.trans' h⟩
    | _ => simp only [assembleProduct, h1, ite_false]; exact ⟨by simp [Term.negBases], .product c⟩
  | _ :: _ :: _ => exact ⟨fun b => by simp [assembleProduct, Term.negBases], fun h => .product c h⟩

/-- `N` of a list of terms depends only on its elements. -/
private theorem negBasesList_perm {ts ts' : List Term} (h : ts.Perm ts') {x : Term} :
    x ∈ Term.negBasesList ts ↔ x ∈ Term.negBasesList ts' := by simp only [mem_negBasesList, h.mem_iff]

/-- The product of parts whose exponents are not 0 has their `N`, and is built from their terms. -/
public theorem buildProduct_bases {o : Orders} {me : ℕ} {p : ProductParts} {u : Term}
    (hp : ∀ x ∈ p.items, x.2 ≠ 0) (h : buildProduct o me p = .value u) :
    (∀ b, b ∈ u.negBases ↔ b ∈ Term.negBasesList (partsTerms p)) ∧ NodesFrom (partsTerms p) u := by
  unfold buildProduct at h; obtain ⟨p', hs, h⟩ := bind_eq_value.1 h
  obtain ⟨hN, -, hn⟩ := settleItems_bases _ p p' hs hp
  generalize hF : p'.items.map itemFactor = F at h
  have hFn : ∀ f ∈ F ++ p'.ones, NodesFrom (partsTerms p') f := fun f hf => by
    rcases List.mem_append.1 hf with hf | hf
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (hF ▸ hf)
      unfold itemFactor; split
      · exact .of_mem (List.mem_append_left _ (List.mem_map_of_mem hx)) (by simp [Term.nodes,
          mem_nodes_self])
      · exact .self (List.mem_append_left _ (List.mem_map_of_mem hx))
    · exact .self (List.mem_append_right _ hf)
  suffices H : (∀ b, b ∈ u.negBases ↔ b ∈ Term.negBasesList (F ++ p'.ones)) ∧
      NodesFrom (F ++ p'.ones) u by
    refine ⟨fun b => ((H.1 b).trans ?_).trans (hN b), (H.2.trans' hFn).trans' hn⟩
    have e : ∀ x : Term × ℤ, (itemFactor x).negBases = (Term.power x.1 x.2).negBases := fun x => by
      unfold itemFactor; split <;> simp_all [negBases_power_pos zero_le_one]
    subst hF; simp [partsTerms, mem_negBasesList, e]
  have hBn : ∀ b ∈ Term.negBasesList (F ++ p'.ones), NodesFrom (F ++ p'.ones) b := fun b hb => by
    obtain ⟨f, hf, hb⟩ := mem_negBasesList.1 hb; exact .of_mem hf (negBases_mem_nodes hb)
  split at h <;> simp only [pure_value, Result.value.injEq] at h <;> subst h
  · exact ⟨fun x => ((negBases_witnesses o _ (.number 0) x).1.trans (negBases_maxRecips o fun _ hb =>
      (negBasesList_closed hb).1)).trans ⟨fun h => h.elim id fun ⟨_, hb, hx⟩ =>
      (negBasesList_closed hb).2 x hx, .inl⟩, (nodesFrom_witnesses fun b hb => hBn b (maxBases_subset hb)).1⟩
  · have hU : ∀ b ∈ uncovered (Term.negBasesList p'.ones) (Term.negBasesList F),
        b ∈ Term.negBasesList p'.ones := fun b hb => (List.mem_filter.1 hb).1
    have hp := perm_sortBy (fun f g => Key.cmp o f.key g.key)
      (F ++ (maxBases o (uncovered (Term.negBasesList p'.ones) (Term.negBasesList F))).map Term.oneOf)
    refine ⟨fun x => ?_, (assembleProduct_bases _ _).2 fun f hf => ?_⟩
    · have ho : ∀ bs : List Term, x ∈ Term.negBasesList (bs.map Term.oneOf) ↔
          x ∈ Term.negBasesList (bs.map Term.reciprocal) := fun bs => by
        simp [mem_negBasesList, negBases_oneOf]
      rw [(assembleProduct_bases _ _).1, negBasesList_perm hp, negBasesList_append,
        negBasesList_append, List.mem_append, List.mem_append, ho,
        negBases_maxRecips o fun b hb => (negBasesList_closed (hU b hb)).1]
      refine ⟨fun h => h.imp_right fun h => h.elim (hU x) fun ⟨b, hb, hx⟩ =>
        (negBasesList_closed (hU b hb)).2 x hx, fun h => ?_⟩
      by_cases hx : x ∈ Term.negBasesList F
      · exact .inl hx
      · exact h.imp_right fun h => .inl (List.mem_filter.2 ⟨h, by simpa using hx⟩)
    · rcases List.mem_append.1 (hp.mem_iff.1 hf) with hf | hf
      · exact .self (List.mem_append_left _ hf)
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hf
        exact ((hBn b (by simpa using .inr (hU b (maxBases_subset hb)))).power _).power _

/-- A product: `N` of the result is `N` of the operands; its nodes are built or of an operand. -/
public theorem mkProduct_bases {o : Orders} {me : ℕ} {ts : List Term} {u : Term}
    (h : mkProduct o me ts = .value u) :
    (∀ b, b ∈ u.negBases ↔ b ∈ Term.negBasesList ts) ∧ NodesFrom ts u := by
  unfold mkProduct at h; split at h; · cases h
  obtain ⟨p, hp, h⟩ := bind_eq_value.1 h
  obtain ⟨hN, hi, hn⟩ := productParts_bases hp
  obtain ⟨h1, h2⟩ := buildProduct_bases hi h
  exact ⟨fun b => (h1 b).trans (hN b), h2.trans' hn⟩

/-! ## Powers -/

/-- `f ^ k` merges at most once, so it has `N(f)` and the bases it introduces; built from `f`. -/
public theorem mergedPower_bases {o : Orders} {me : ℕ} {f u : Term} {k : ℤ}
    (hf : f.factorOk = true) (hc : ∀ c i, f = .power c i → canonicalPower c i = true)
    (h : mergedPower o me f k = .value u) :
    (∀ x, x ∈ u.negBases ↔ x ∈ f.negBases ∨ (k < 0 ∧ x ∈ f.introducedBase)) ∧
      NodesFrom [f] u := by
  obtain ⟨⟨c, j⟩, hm, h⟩ := bind_eq_value.1 h
  have hs : (∀ x, x ∈ u.negBases ↔ x ∈ (Term.power c j).negBases) ∧ NodesFrom [c] u := by
    dsimp only at h
    split at h
    · cases h; subst j; exact ⟨fun x => by rw [negBases_power_pos zero_le_one], .self (by simp)⟩
    split at h
    · cases h; subst j; exact ⟨fun x => by rw [negBases_power_pos le_rfl, (negBases_witnesses o [] c x).2.2],
        nodesFrom_powerZero o c⟩
    · obtain ⟨hN, hn⟩ := buildProduct_bases (by simpa using ‹¬j = 0›) h
      exact ⟨fun x => by simpa [partsTerms, Term.negBasesList] using hN x,
        hn.trans' (by simpa [partsTerms] using NodesFrom.power j (.self (List.mem_singleton_self c)))⟩
  have hmc : (c = f ∧ j = k ∧ ∀ c' i, f = .power c' i → i < 0 ∧ k ≤ 0) ∨
      ∃ i, f = .power c i ∧ (0 ≤ i ∨ 0 < k) ∧ j = i * k := by
    cases f with
    | power c' i =>
      rw [mergePowers] at hm
      split at hm
      · rename_i hmi
        rw [mergeCondition_iff] at hmi
        unfold checkExponent at hm; split at hm; · cases hm
        suffices e : c = c' ∧ j = i * k from .inr ⟨i, e.1 ▸ rfl, hmi, e.2⟩
        cases c' with
        | power d l =>
          have hl := hc _ _ rfl
          simp only [canonicalPower, Bool.and_eq_true, Bool.not_eq_true'] at hl
          have hl := hl.2.1
          rw [← Bool.not_eq_true, mergeCondition_iff] at hl
          have : i * k ≤ 0 := by
            rcases (show i = 0 ∨ i < 0 ∧ 0 < k by omega) with h | ⟨h1, h2⟩
            exacts [by simp [h], by nlinarith]
          rw [mergePowers, show mergeCondition l (i * k) = false by
            rw [← Bool.not_eq_true, mergeCondition_iff]; omega] at hm
          simpa [eq_comm] using hm
        | _ =>
          simp only [mergePowers, Result.value.injEq, Prod.mk.injEq] at hm; exact ⟨hm.1.symm, hm.2.symm⟩
      · simp only [Result.value.injEq, Prod.mk.injEq] at hm
        refine .inl ⟨hm.1.symm, hm.2.symm, fun _ _ he => ?_⟩
        cases he; have := ‹¬mergeCondition i k = true›; rw [mergeCondition_iff] at this; omega
    | _ =>
      simp only [mergePowers, Result.value.injEq, Prod.mk.injEq] at hm
      exact .inl ⟨hm.1.symm, hm.2.symm, fun _ _ he => by cases he⟩
  rcases hmc with ⟨rfl, rfl, hn⟩ | ⟨i, rfl, hmc, rfl⟩
  · refine ⟨fun x => (hs.1 x).trans ?_, hs.2⟩
    rw [mem_negBases_power]
    cases c with
    | sum c ms =>
      have : primitivePart c ms = .sum c ms := by
        simp [Term.factorOk] at hf; simp [primitivePart, scaleSum, hf]
      simp [Term.introducedBase, this, Term.isConstant, or_comm]
    | power d i => simp [Term.introducedBase, (hn d i rfl).1, Term.isConstant, or_comm]
    | _ => simp_all [Term.introducedBase, Term.factorOk, Term.isConstant, or_comm]
  · refine ⟨fun x => (hs.1 x).trans ?_, hs.2.trans' fun t ht => by
      rw [List.mem_singleton.1 ht]
      exact .of_mem (List.mem_singleton_self _) (by simp [Term.nodes, mem_nodes_self])⟩
    rw [mem_negBases_power, mem_negBases_power]
    rcases lt_trichotomy i 0 with hi | rfl | hi
    · have hik : i * k < 0 := mul_neg_of_neg_of_pos hi (by omega)
      have hk : ¬k < 0 := by omega
      simp [Term.introducedBase, hi, hik, hk]
    · simp [Term.introducedBase]
    · have hik : i * k < 0 ↔ k < 0 := ⟨fun h => by nlinarith, fun h => by nlinarith⟩
      simp [Term.introducedBase, hik, hi.ne', not_lt.2 hi.le]
      tauto

/-- A power that is a value: an exponent within the bound, a base that is a value, and a power
of a number, the exponent 1, the exponent 0, or else distributed. -/
public theorem mkPower_cases {o : Orders} {me : ℕ} {b u : Term} {k : ℤ}
    (h : mkPower o me b k = .value u) :
    ¬exponentBound me < k.natAbs ∧ b.isCondition = false ∧
      ((∃ r q, b = .number r ∧ u = .number q ∧
          Result.ofOutcome (Kalyx.Spec.Fields.ratPowOp r k) = .value q) ∨
        (k = 1 ∧ u = b) ∨ (k = 0 ∧ u = powerZero o b) ∨
        k ≠ 1 ∧ k ≠ 0 ∧ (∀ r, b ≠ .number r) ∧ distributedPower o me b k = .value u) := by
  unfold mkPower checkExponent at h
  split at h; · cases h
  split at h; · cases h
  rename_i hk hc
  refine ⟨hk, by simpa using hc, ?_⟩
  cases b with
  | number r => obtain ⟨q, hq, rfl⟩ := map_eq_value.1 h; exact .inl ⟨r, q, rfl, rfl, hq⟩
  | _ =>
    simp only at h
    split at h; · cases h; exact .inr (.inl ⟨by assumption, rfl⟩)
    split at h; · cases h; exact .inr (.inr (.inl ⟨by assumption, rfl⟩))
    exact .inr (.inr (.inr ⟨by assumption, by assumption, nofun, h⟩))

/-- A power of a canonical base: `N` of the base and, for a negative exponent, the bases that
the power introduces, are `N` of the result; its nodes are built or of the base. -/
public theorem mkPower_bases {o : Orders} {me : ℕ} {R : RegistryRules} {b u : Term} {k : ℤ}
    (hb : Term.Canonical o me R b) (h : mkPower o me b k = .value u) :
    (∀ x, x ∈ u.negBases ↔ x ∈ b.negBases ∨ (k < 0 ∧ x ∈ b.introducedBases)) ∧
      NodesFrom [b] u := by
  have hnode : ∀ x ∈ b.nodes, x.nodeOk o me R = true := List.all_eq_true.1 hb.1
  have hpw : ∀ c i, b = .power c i → canonicalPower c i = true := fun c i he => by
    subst he; simpa [Term.nodeOk] using hnode _ (mem_nodes_self _)
  rcases mkPower_cases h with ⟨-, hc, ⟨r, q, rfl, rfl, -⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h1, h0, hq, h⟩⟩
  · exact ⟨fun x => by simp [Term.negBases, Term.introducedBases, Term.introducedBase], .number q⟩
  · exact ⟨fun x => by simp, .self (List.mem_singleton_self _)⟩
  · exact ⟨fun x => by simp [(negBases_witnesses o [] b x).2.2], nodesFrom_powerZero o b⟩
  cases b with
  | product c fs =>
    simp only [distributedPower] at h
    obtain ⟨ck, -, h⟩ := bind_eq_value.1 h
    obtain ⟨rs, hrs, h⟩ := bind_eq_value.1 h
    obtain ⟨hN, hn⟩ := mkProduct_bases h
    obtain ⟨hl, hr⟩ := mapM_mem hrs
    have hcp : canonicalProduct o c fs = true := by simpa [Term.nodeOk] using hnode _ (mem_nodes_self _)
    simp only [canonicalProduct, Bool.and_eq_true, List.all_eq_true] at hcp
    have hfr : ∀ f ∈ fs, ∀ r, mergedPower o me f k = .value r →
        (∀ x, x ∈ r.negBases ↔ x ∈ f.negBases ∨ (k < 0 ∧ x ∈ f.introducedBase)) ∧
          NodesFrom [f] r := fun f hf r h => mergedPower_bases (hcp.1.1.1 f hf) (fun c i he => by
        subst he
        simpa [Term.nodeOk] using hnode _ (nodes_trans (mem_nodes_factor hf) (mem_nodes_self _))) h
    refine ⟨fun x => ?_, hn.trans' fun t ht => ?_⟩
    · simp only [hN, Term.negBasesList, Term.negBases, List.nil_append, Term.introducedBases,
        List.mem_flatMap, mem_negBasesList]
      constructor
      · rintro ⟨r, hr', hx⟩
        obtain ⟨f, hf, hfr'⟩ := hr r hr'
        rcases ((hfr f hf r hfr').1 x).1 hx with hx | ⟨hk, hx⟩
        exacts [.inl ⟨f, hf, hx⟩, .inr ⟨hk, f, hf, hx⟩]
      · rintro (⟨f, hf, hx⟩ | ⟨hk, f, hf, hx⟩) <;> obtain ⟨r, hr', hfr'⟩ := hl f hf <;>
          exact ⟨r, hr', ((hfr f hf r hfr').1 x).2 (by tauto)⟩
    · rcases List.mem_cons.1 ht with rfl | ht
      · exact .number _
      obtain ⟨f, hf, hfr'⟩ := hr t ht
      exact (hfr f hf t hfr').2.trans' fun g hg => by
        rw [List.mem_singleton.1 hg]; exact .of_mem (List.mem_singleton_self _) (mem_nodes_factor hf)
  | sum c ms =>
    simp only [distributedPower] at h
    obtain ⟨ck, -, h⟩ := bind_eq_value.1 h
    obtain ⟨hN, hn⟩ := buildProduct_bases (by simpa using h0) h
    refine ⟨fun x => ?_, hn.trans' (by simpa [partsTerms] using .power k (scaleSum_bases _ c ms).2)⟩
    have hpc : (scaleSum (sumContent c ms)⁻¹ c ms).isConstant = false := rfl
    simp [hN, partsTerms, Term.negBasesList, mem_negBases_power, primitivePart, hpc,
      (scaleSum_bases _ c ms).1, Term.introducedBases, Term.introducedBase, or_comm]
  | number r => exact absurd rfl (hq r)
  | condition => simp [Term.isCondition] at hc
  | _ =>
    simp only [distributedPower] at h
    simpa [Term.introducedBases] using mergedPower_bases (by simp [Term.factorOk]) hpw h

/-! ## Negations, differences and quotients -/

/-- A negation: `N` of the result is `N` of the operand, and its nodes are built or of it. -/
public theorem mkNegate_bases {o : Orders} {me : ℕ} {t u : Term}
    (h : mkNegate o me t = .value u) :
    (∀ b, b ∈ u.negBases ↔ b ∈ t.negBases) ∧ NodesFrom [t] u := by
  obtain ⟨h1, h2⟩ := mkProduct_bases h
  exact ⟨fun b => by simpa [Term.negBasesList, Term.negBases] using h1 b,
    h2.trans' (by simp [NodesFrom.number, NodesFrom.self])⟩

/-- A difference: `N` of the result is `N` of the operands; its nodes are built or of one. -/
public theorem mkSubtract_bases {o : Orders} {me : ℕ} {a b u : Term}
    (h : mkSubtract o me a b = .value u) :
    (∀ x, x ∈ u.negBases ↔ x ∈ Term.negBasesList [a, b]) ∧ NodesFrom [a, b] u := by
  obtain ⟨nb, hn, h⟩ := bind_eq_value.1 h
  obtain ⟨h1, h2⟩ := mkSum_bases h
  obtain ⟨hn1, hn2⟩ := mkNegate_bases hn
  exact ⟨fun x => by simpa [Term.negBasesList, hn1] using h1 x,
    h2.trans' (by simpa using ⟨.self (by simp), hn2.mono (by simp)⟩)⟩

/-- A quotient by a canonical divisor: `N` of the operands and the bases that the power `-1` of
the divisor introduces are `N` of the result; its nodes are built or of an operand. -/
public theorem mkDivide_bases {o : Orders} {me : ℕ} {R : RegistryRules} {a b u : Term}
    (hb : Term.Canonical o me R b) (h : mkDivide o me a b = .value u) :
    (∀ x, x ∈ u.negBases ↔ x ∈ Term.negBasesList [a, b] ∨ x ∈ b.introducedBases) ∧
      NodesFrom [a, b] u := by
  obtain ⟨r, hr, h⟩ := bind_eq_value.1 h
  obtain ⟨h1, h2⟩ := mkProduct_bases h
  obtain ⟨hr1, hr2⟩ := mkPower_bases hb hr
  exact ⟨fun x => by simp [h1, Term.negBasesList, hr1, or_assoc],
    h2.trans' (by simpa using ⟨.self (by simp), hr2.mono (by simp)⟩)⟩

/-! ## Calls -/

/-- The item of a call with the exponent 1 is settled as it is. -/
private theorem reduceItem_call_one {me : ℕ} (h1 : 1 ≤ me) (hd : Head) (args : List Term) :
    reduceItem me (.call hd args, 1) = .value (⟨1, [(.call hd args, 1)], []⟩, []) := by
  have hb : ¬exponentBound me < 1 := by unfold exponentBound; omega
  simp only [reduceItem, checkExponent, Int.natAbs_one, hb, ite_false, Term.imaginaryUnit,
    one_ne_zero, reduceCtorEq]
  cases hr : rootOf (.call hd args) with
  | none => rfl
  | some p => simp only [show ¬((p.2 : ℤ) ≤ 1) by have := (rootOf_some hr).1; omega, ite_false]

/-- Two different calls multiply into the product of both, sorted, and add into their sum. -/
private theorem two_calls (o : Orders) (me : ℕ) (hT : TotalCmp (Term.cmp o)) (h1 : 1 ≤ me)
    (h g : Head) (args brgs : List Term) (hne : Term.call h args ≠ .call g brgs) :
    mkProduct o me [.call h args, .call g brgs] =
      .value (.product 1 (sortBy (Term.cmp o) [.call h args, .call g brgs])) ∧
    mkSum o [.call h args, .call g brgs] =
      .value (.sum 0 (sortBy (monomialCmp o) [(1, .call h args), (1, .call g brgs)])) := by
  have := hT.1; have := hT.2
  have hr := reduceItem_call_one h1
  have hne' := Ne.symm hne
  have hsw : Term.cmp o (.call g brgs) (.call h args) =
      (Term.cmp o (.call h args) (.call g brgs)).swap := Std.OrientedCmp.eq_swap
  rcases hcmp : Term.cmp o (.call h args) (.call g brgs) <;> rw [hcmp] at hsw <;>
    first
    | exact absurd (Std.LawfulEqCmp.eq_of_compare hcmp) hne
    | exact ⟨by simp [mkProduct, Term.isCondition, productParts, factorParts, itemParts,
        ProductParts.append, ProductParts.unit, buildProduct, settleItems, mergeItems, sortBy,
        insertBy, mergeAdjacent, Key.cmp, Key.of, Term.isConstant, hcmp, hr, hne, hne', itemFactor,
        Term.key, maxBases, sortedTerms, uncovered, Term.negBasesList, Term.negBases,
        assembleProduct, hsw], by simp [mkSum, Term.isCondition, sumParts, mergeMonomials,
        cancelMonomials, sortBy, insertBy, mergeAdjacent, monomialCmp, hcmp, hne, hne', maxBases,
        sortedTerms, uncovered, Term.negBasesPairs, assembleSum]⟩

/-- A call multiplied by itself is its square, and added to itself is twice the call. -/
private theorem call_twice (o : Orders) (me : ℕ) (h : Head) (args : List Term) :
    mkProduct o me [.call h args, .call h args] = mkPower o me (.call h args) 2 ∧
      mkSum o [.call h args, .call h args] = .value (.product 2 [.call h args]) := by
  refine ⟨?_, by simp [mkSum, Term.isCondition, sumParts, mergeMonomials, cancelMonomials, sortBy,
    insertBy, mergeAdjacent, maxBases, sortedTerms, uncovered, Term.negBasesPairs, assembleSum,
    Term.coreFactors]; norm_num⟩
  have hq : mkProduct o me [.call h args, .call h args] =
      buildProduct o me ⟨1, [(.call h args, 2)], []⟩ := by
    simp only [mkProduct, Term.isCondition, List.any_cons, List.any_nil, Bool.or_false,
      Bool.false_eq_true, ite_false]
    simp [productParts, factorParts, itemParts, ProductParts.append, ProductParts.unit,
      buildProduct, Term.depthList, settleItems, mergeItems, sortBy, insertBy, mergeAdjacent]
  rw [hq, show mkPower o me (.call h args) 2 =
      checkExponent me 2 (fun _ => buildProduct o me ⟨1, [(.call h args, 2)], []⟩) by
    simp [mkPower, checkExponent, Term.isCondition, distributedPower, mergedPower, mergePowers],
    checkExponent]
  split
  · have hlt : exponentBound me ≤ 1 := by simp at *; omega
    simp [buildProduct, settleItems, mergeItems, sortBy, insertBy, mergeAdjacent, reduceItem,
      checkExponent, hlt]
  · rfl

/-- Proves `CallsAreAtoms`: results build their nodes from their operands; calls are atoms. -/
public theorem callsAreAtoms_holds : CallsAreAtoms := fun o me _ ho _ =>
  ⟨fun _ _ _ h => callsWithin_of_nodesFrom (mkSum_bases h).2,
    fun _ _ _ h => callsWithin_of_nodesFrom (mkProduct_bases h).2,
    fun _ _ _ hb h => callsWithin_of_nodesFrom (mkPower_bases hb h).2,
    fun h args _ => call_twice o me h args,
    fun h args g brgs _ _ hne h1 => two_calls o me (termCmp_total o ho) h1 h g args brgs hne⟩

/-! ## The bases of negative powers -/

/-- A call that the rule of `piecewise` does not select keeps `N` of its canonical arguments. -/
private theorem mkCall_bases {o : Orders} {me : ℕ} {R : RegistryRules}
    (hR : R.Closed (fun me => Term.Canonical o me R) Term.negBases) {h : Head} {args : List Term}
    {u : Term} (ha : ∀ a ∈ args, Term.Canonical o me R a)
    (hp : h = Head.piecewise → piecewiseBranch args = none) (hu : mkCall me R h args = .value u) :
    BasesKept args u := by
  unfold mkCall at hu
  rw [show (if h = Head.piecewise then piecewiseBranch args else none) = none by
    split <;> simp_all] at hu
  split at hu; · cases hu
  intro b hb
  cases hr : R.apply me h args <;> simp only [hr, Result.value.injEq, reduceCtorEq] at hu <;>
    subst hu
  exacts [hb, (hR me h args _ ha hr).2.2 b hb]

/-- A negation of a canonical term reads in a sum as its opposite, constant and coefficients. -/
@[expose] public def NegationReadsOpposite : Prop :=
  ∀ (o : Orders) (me : ℕ) (R : RegistryRules), o.Total → ∀ t nb, Term.Canonical o me R t →
    mkNegate o me t = .value nb → (sumParts [nb]).1 = -(sumParts [t]).1 ∧
      ∀ s, coefficientOf s (sumParts [nb]).2 = -coefficientOf s (sumParts [t]).2

/-- `t - t` is the zero witness of `N(t)` when negations read as opposites: no coefficient left. -/
private theorem subtract_self (hneg : NegationReadsOpposite) {o : Orders} {me : ℕ}
    {R : RegistryRules} (ho : o.Total) {t u : Term} (ht : Term.Canonical o me R t)
    (h : mkSubtract o me t t = .value u) : u = zeroWitness (maxBases o t.negBases) := by
  have hT := termCmp_total o ho
  obtain ⟨nb, hn, h⟩ := bind_eq_value.1 h
  obtain ⟨hc, hm⟩ := hneg o me R ho t nb ht hn
  have hN := (mkSum_bases h).1
  unfold mkSum at h; split at h; · cases h
  cases h
  generalize hM : mergeMonomials o (sumParts [t, nb]).2 = M at hN
  have hz : ∀ m ∈ M, m.1 = 0 := fun m hm' => by
    rw [← hM, mem_mergeMonomials hT] at hm'
    rw [hm'.2, Sums.sumParts_cons, Sums.coefficientOf_append, hm, add_neg_cancel]
  have hb : maxBases o (Term.negBasesPairs M) = maxBases o t.negBases := maxBases_congr hT fun x => by
    rw [← (cancelMonomials_bases o M).1, ← (assembleSum_bases _ _).1, hN]
    simp [Term.negBasesList, (mkNegate_bases hn).1]
  have hcz : cancelMonomials o M = if maxBases o (Term.negBasesPairs M) = [] then []
      else [(0, witnessCore (maxBases o (Term.negBasesPairs M)))] := by
    have h1 : M.filter (fun m => decide (m.1 ≠ 0)) = [] := List.filter_eq_nil_iff.2 (by simpa using hz)
    have h2 : M.filter (fun m => decide (m.1 = 0)) = M := List.filter_eq_self.2 (by simpa using hz)
    unfold cancelMonomials; dsimp only; rw [h1, h2]
    simp only [uncovered, Term.negBasesPairs, List.contains_nil, Bool.not_false, List.filter_true]
    split <;> simp_all [insertBy]
  rw [show (sumParts [t, nb]).1 = 0 by rw [Sums.sumParts_cons, hc, add_neg_cancel], hcz, ← hb]
  match maxBases o (Term.negBasesPairs M) with
  | [] => simp [assembleSum, zeroWitness]
  | [b] => simp [assembleSum, zeroWitness, witnessCore, Term.reciprocal, Term.coreFactors]
  | b :: c :: bs => simp [assembleSum, zeroWitness, witnessCore, Term.coreFactors]

/-- Proves `ConstructorsKeepNegativeBases`, given that negations read as opposites. -/
public theorem constructorsKeepNegativeBases_of (hneg : NegationReadsOpposite) :
    ConstructorsKeepNegativeBases := fun o me R ho hR =>
  have kept : ∀ {ts u}, (∀ b, b ∈ u.negBases ↔ b ∈ Term.negBasesList ts) → BasesKept ts u :=
    fun h b hb => (h b).2 hb
  ⟨fun _ _ _ h => kept (mkSum_bases h).1, fun _ _ _ h => kept (mkProduct_bases h).1,
    fun _ _ _ hb h x hx => ((mkPower_bases hb h).1 x).2 (.inl (by simpa [Term.negBasesList] using hx)),
    fun _ _ _ h x hx => ((mkNegate_bases h).1 x).2 (by simpa [Term.negBasesList] using hx),
    fun _ _ _ _ _ h => kept (mkSubtract_bases h).1,
    fun _ _ _ _ hb h x hx => ((mkDivide_bases hb h).1 x).2 (.inl hx),
    fun _ _ _ ha hp hu => mkCall_bases hR ha hp hu,
    fun _ _ _ hb hk h c hc => ((mkPower_bases hb h).1 c).2 (.inr ⟨hk, hc⟩),
    fun _ _ _ _ hb h c hc => ((mkDivide_bases hb h).1 c).2 (.inr hc),
    fun t => by simp [Term.hasNegativePower], fun _ _ ht h => subtract_self hneg ho ht h,
    fun t hc hn => by cases t <;> simp_all [mkPower, checkExponent]⟩

end Kalyx.Proofs.Terms.Bases
