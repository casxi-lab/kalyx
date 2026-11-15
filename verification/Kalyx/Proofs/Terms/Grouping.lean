module

public import Kalyx.Proofs.Terms.Settle
public import Kalyx.Proofs.Terms.Products
public import Kalyx.Proofs.Terms.Bases

/-!
# Products ignore grouping; powers of roots

Two conjuncts, through parts that settle alike (`Settle.SettleEq`): a product of canonical
operands does not depend on their grouping when the constructions succeed
(`productsIgnoreGrouping`, the grouping of products in `SumsAndProductsIgnoreOrderAndGrouping`),
since a built product reads back as parts that settle like the parts it is built from; and a
power `k ≥ n` of a root `ⁿ√u` of a literal degree is `u ^ ⌊k/n⌋ (ⁿ√u) ^ (k mod n)` when both
sides succeed (`powersOfRoots`, the powers of roots in `MergingAddsCoefficientsAndExponents`),
since the first round reduces the root this way.
-/

namespace Kalyx.Proofs.Terms.Grouping

open Kalyx.Spec.Terms Kalyx.Statements.Terms Kalyx.Proofs.Terms Kalyx.Proofs.Terms.Settle
  Kalyx.Proofs.Terms.Products Kalyx.Proofs.Terms.Bases
open Kalyx.Spec.Fields (ratPowOp ratPow)

variable {o : Orders} {me : ℕ} {R : RegistryRules}

/-- A built product reads back as parts that settle alike, of that shape off the coefficient 0. -/
private theorem built (ho : o.Total) {P A : ProductParts} {a : Term}
    (hP : P.coefficient ≠ 0 → ∀ x ∈ P.items, RootShape o me R x)
    (h : buildProduct o me P = .value a) (hA : factorParts me 1 a = .value A) :
    SettleEq o P A ∧ (A.coefficient ≠ 0 → ∀ x ∈ A.items, RootShape o me R x) := by
  have hK := keyCmp_total o ho
  rw [buildProduct_eq] at h
  obtain ⟨σ, hσ, rfl⟩ := map_eq_value.1 h
  have e := SettleEq.of_settle hK hσ P.ones
  by_cases hc : σ.coefficient = 0
  · unfold finish at hA; dsimp only at hA; rw [ite_eq_left hc] at hA
    exact ⟨e.zero hc (zeroWitness_parts hA), fun h => absurd (zeroWitness_parts hA) h⟩
  have hs := settleItems_shape hK hσ (hP fun h0 => hc (settleItems_coeff hσ h0))
  have hq : productParts me [finish o ⟨σ.coefficient, σ.items, P.ones ++ σ.ones⟩] =
      .value ⟨A.coefficient * 1, A.items ++ [], A.ones ++ []⟩ := by
    rw [productParts_cons, hA]; rfl
  obtain ⟨h1, h2⟩ := productParts_finish o me (s := ⟨σ.coefficient, σ.items, P.ones ++ σ.ones⟩) hc
    (fun x hx => (hs x hx).1) hq
  simp only [mul_one, List.append_nil] at h1 h2
  exact ⟨e.trans (SettleEq.of_perm hK h1.symm h2.symm), fun _ x hx => hs x (h2.subset hx)⟩

/-- `mapM` over two lists. -/
private theorem mapM_append_value {α β : Type} {f : α → Result β} {l₁ l₂ : List α} {rs : List β}
    (h : (l₁ ++ l₂).mapM f = .value rs) :
    ∃ r₁ r₂, l₁.mapM f = .value r₁ ∧ l₂.mapM f = .value r₂ ∧ rs = r₁ ++ r₂ := by
  rw [List.mapM_append] at h
  obtain ⟨r₁, h₁, h⟩ := bind_eq_value.1 h; obtain ⟨r₂, h₂, h⟩ := bind_eq_value.1 h
  exact ⟨r₁, r₂, h₁, h₂, (Result.value.inj h).symm⟩

/-- Products do not depend on the grouping of canonical operands, when the constructions succeed. -/
public theorem productsIgnoreGrouping (o : Orders) (me : ℕ) (R : RegistryRules) (ho : o.Total) :
    ∀ ts₁ ts₂ ts₃ s u u', (∀ t ∈ ts₁ ++ ts₂ ++ ts₃, Term.Canonical o me R t) →
      mkProduct o me ts₂ = .value s → mkProduct o me (ts₁ ++ ts₂ ++ ts₃) = .value u →
      mkProduct o me (ts₁ ++ s :: ts₃) = .value u' → u = u' := by
  intro ts₁ ts₂ ts₃ s u u' hc hs hu hu'
  have hK := keyCmp_total o ho
  obtain ⟨hv, P, hP, hu⟩ := mkProduct_split hu
  obtain ⟨-, P', hP', hu'⟩ := mkProduct_split hu'
  obtain ⟨-, B, hB, hs'⟩ := mkProduct_split hs
  obtain ⟨Ps, hPs, hP₁⟩ := bind_eq_value.1 hP
  obtain ⟨Ps', hPs', hP₁'⟩ := bind_eq_value.1 hP'
  obtain ⟨Bs, hBs, hB₁⟩ := bind_eq_value.1 hB
  cases hP₁; cases hP₁'; cases hB₁
  obtain ⟨Q, Ps₃, hQ, h₃, rfl⟩ := mapM_append_value hPs
  obtain ⟨Ps₁, Ps₂, h₁, h₂, rfl⟩ := mapM_append_value hQ
  obtain ⟨Ps₁', Ss, h₁', hS, rfl⟩ := mapM_append_value hPs'
  rw [h₁] at h₁'; cases h₁'; rw [h₂] at hBs; cases hBs
  rw [List.mapM_cons] at hS
  obtain ⟨S, hS₁, hSs⟩ := bind_eq_value.1 hS
  obtain ⟨Ps₃', h₃', hSs⟩ := bind_eq_value.1 hSs
  rw [h₃] at h₃'; cases h₃'; cases hSs
  have hsh := productParts_shape (fun t ht => ⟨hc t (by simp [ht]), hv t (by simp [ht])⟩) hB
  have e := (built ho (fun _ => hsh) hs' hS₁).1
  have hE : SettleEq o ((Ps₁ ++ Bs ++ Ps₃).foldl ProductParts.append ProductParts.unit)
      ((Ps₁ ++ S :: Ps₃).foldl ProductParts.append ProductParts.unit) := by
    simp only [List.foldl_append, List.foldl_cons]
    refine SettleEq.foldl hK (List.forall₂_same.2 fun x _ => SettleEq.of_perm hK rfl (.refl _)) ?_
    refine (SettleEq.of_perm hK ?_ ?_).trans ((SettleEq.of_perm hK rfl (.refl _)).append hK e)
    · simp [foldl_append, ProductParts.append, ProductParts.unit]
    · simp [foldl_append, ProductParts.append, ProductParts.unit]
  rw [buildProduct_eq] at hu hu'
  obtain ⟨σ, hσ, rfl⟩ := map_eq_value.1 hu
  obtain ⟨σ', hσ', rfl⟩ := map_eq_value.1 hu'
  obtain ⟨e1, e2⟩ := hE.settle hK hσ hσ'
  refine finish_eq ho e1 e2 fun b => (settled_N hP hσ b).trans (Iff.trans ?_
    (settled_N hP' hσ' b).symm)
  have := (mkProduct_bases hs).1 b
  simp only [mem_negBasesList, List.mem_append, List.mem_cons, or_and_right, exists_or,
    exists_eq_left] at this ⊢
  rw [this, or_assoc]

/-! ## Powers of roots -/

/-- A power `j ≥ 0` of a root: the power 0, the root, or the product of the item. -/
private theorem root_pow {s u b : Term} {n : ℕ} {j : ℤ} (hr : rootOf s = some (u, n)) (hj : 0 ≤ j)
    (h : mkPower o me s j = .value b) : (j = 0 ∧ b = powerZero o s) ∨ (j = 1 ∧ b = s) ∨
      (2 ≤ j ∧ buildProduct o me ⟨1, [(s, j)], []⟩ = .value b) := by
  obtain ⟨-, hd, rest, rfl, -⟩ := rootOf_some hr
  unfold mkPower checkExponent at h; split at h; · cases h
  by_cases h1 : j = 1; · subst h1; simp [Term.isCondition] at h; exact .inr (.inl ⟨rfl, h.symm⟩)
  by_cases h0 : j = 0; · subst h0; simp [Term.isCondition] at h; exact .inl ⟨rfl, h.symm⟩
  simp only [Term.isCondition, h1, h0, ite_false, Bool.false_eq_true, distributedPower,
    mergedPower, mergePowers, bind_value] at h
  exact .inr (.inr ⟨by omega, h⟩)

/-- The power 0 of a term reads back with the coefficient 1 and no items. -/
private theorem powerZero_parts {t : Term} {B : ProductParts}
    (h : factorParts me 1 (powerZero o t) = .value B) : B.coefficient = 1 ∧ B.items = [] := by
  unfold powerZero at h; split at h
  · cases h; simp
  · simp [Term.oneOf, factorParts, itemParts] at h; subst h; simp
  · obtain ⟨ps, hps, h⟩ := bind_eq_value.1 h; cases h
    have hp : ∀ p ∈ ps, p.coefficient = 1 ∧ p.items = [] := fun p hp => by
      obtain ⟨f, hf, e⟩ := (mapM_mem hps).2 p hp
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hf; simp [Term.oneOf, itemParts] at e; subst e; simp
    have hc : (ps.map (·.coefficient)).prod = 1 := List.prod_eq_one fun x hx => by
      obtain ⟨p, hp', rfl⟩ := List.mem_map.1 hx; exact (hp p hp').1
    simp only [foldl_append, hc]
    exact ⟨by simp, by simpa using fun p hp' => (hp p hp').2⟩

/-- A power `q ≥ 2` of a canonical factor: the product of its parts, or a power 0 without items. -/
private theorem mergedPower_parts {f a : Term} {q : ℤ} {X : ProductParts} (hq : 2 ≤ q)
    (hf : f.factorOk = true) (hc : Term.nodeOk o me R f = true)
    (h : mergedPower o me f q = .value a) (hX : itemParts me q f = .value X) :
    buildProduct o me X = .value a ∨ (X.coefficient = 1 ∧ X.items = [] ∧ ∃ t, a = powerZero o t) := by
  have h1 : q ≠ 1 := by omega
  have h0 : q ≠ 0 := by omega
  cases f with
  | sum c ms =>
    have hc1 : sumContent c ms = 1 := by simpa [Term.factorOk] using hf
    simp only [itemParts] at hX; cases hX
    left; simpa [mergedPower, mergePowers, primitivePart, scaleSum, hc1, h1, h0] using h
  | power b j =>
    have hcb : canonicalPower b j = true := hc
    by_cases hj : j = 0
    · subst hj; simp only [itemParts, ite_true] at hX; cases hX
      refine .inr ⟨rfl, rfl, ?_⟩
      cases b with
      | power c i =>
        simp [canonicalPower] at hcb
        simp [mergedPower, mergePowers, mergeCondition, checkExponent, hcb] at h
        exact ⟨_, h.symm⟩
      | _ => simp [canonicalPower] at hcb
    · left
      simp only [itemParts, hj, ite_false, checkExponent] at hX; split at hX; · cases hX
      rename_i hb; cases hX
      have hm : mergeCondition j q = true := mergeCondition_iff.2 (.inr (by omega))
      have hb' : mergePowers me b (j * q) = .value (b, j * q) := by
        cases b with
        | power c i =>
          have hi := (by simpa [canonicalPower] using hcb : _ ∧ mergeCondition i j = false ∧ _).2.1
          have : mergeCondition i (j * q) = false := by
            obtain ⟨h1, h2⟩ := mergeCondition_false.1 hi; exact mergeCondition_false.2 ⟨h1, by nlinarith⟩
          simp [mergePowers, this]
        | _ => rfl
      have hjq : j * q ≠ 1 ∧ j * q ≠ 0 := by
        constructor <;> intro e <;> rcases lt_or_gt_of_ne hj with hj | hj <;> nlinarith
      simpa [mergedPower, mergePowers, hm, checkExponent, hb, hb', hjq] using h
  | number | product | condition => simp [Term.factorOk] at hf
  | constant | symbol | call =>
    simp only [itemParts] at hX; cases hX
    left; simpa [mergedPower, mergePowers, h1, h0] using h

/-- Related lists, through a list related to both. -/
private theorem forall₂_chain {α β γ δ : Type} {R₁ : α → β → Prop} {R₂ : α → γ → Prop}
    {R₃ : γ → δ → Prop} {S : β → δ → Prop} : ∀ {l : List α} {bs : List β} {cs : List γ}
    {ds : List δ}, List.Forall₂ R₁ l bs → List.Forall₂ R₂ l cs → List.Forall₂ R₃ cs ds →
      (∀ a ∈ l, ∀ b c d, R₁ a b → R₂ a c → R₃ c d → S b d) → List.Forall₂ S bs ds
  | _, _, _, _, .nil, .nil, .nil, _ => .nil
  | _, _, _, _, .cons h₁ t₁, .cons h₂ t₂, .cons h₃ t₃, h =>
    .cons (h _ (by simp) _ _ _ h₁ h₂ h₃) (forall₂_chain t₁ t₂ t₃ fun a ha => h a (.tail _ ha))

/-- The parts read back from a power `q ≥ 1` of a canonical value settle like its parts. -/
private theorem pow_parts (ho : o.Total) {u a : Term} {q : ℤ} {P A : ProductParts} (hq : 1 ≤ q)
    (hu : Term.Canonical o me R u) (hv : u.isCondition = false) (h : mkPower o me u q = .value a)
    (hP : factorParts me q u = .value P) (hA : factorParts me 1 a = .value A) : SettleEq o P A := by
  have hK := keyCmp_total o ho
  have hsh := factorParts_shape (by omega) hu hv hP
  have hok := List.all_eq_true.1 hu.1 _ (mem_nodes_self _)
  have hrat : ∀ r : ℚ, Result.ofOutcome (ratPowOp r q) = .value (r ^ q) := fun r => by
    simp [ratPowOp, ratPow, Kalyx.Spec.Fields.FieldError.lift, Result.ofOutcome,
      show ¬ q < 0 by omega]
  by_cases hn : ∃ r, u = .number r
  · obtain ⟨r, rfl⟩ := hn
    simp only [mkPower, checkExponent, Term.isCondition, hrat] at h; split at h; · cases h
    cases h; cases hP; cases hA; exact SettleEq.of_perm hK (by simp) (.refl _)
  push Not at hn
  rcases (Bases.mkPower_cases h).2.2 with ⟨r, -, rfl, -⟩ | ⟨rfl, rfl⟩ | ⟨rfl, -⟩ | ⟨h1, -, -, h⟩
  · exact absurd rfl (hn r)
  · rw [hP] at hA; cases hA; exact SettleEq.of_perm hK rfl (.refl _)
  · exact absurd hq (by omega)
  have hq2 : 2 ≤ q := by omega
  cases u with
  | number r => exact absurd rfl (hn r)
  | condition => cases hv
  | sum c ms =>
    simp only [distributedPower, hrat, bind_value] at h
    simp only [factorParts, itemParts] at hP; cases hP
    exact (built ho (fun _ => hsh) h hA).1
  | power _ _ | constant _ | symbol _ | call _ _ =>
    rcases mergedPower_parts hq2 rfl hok h hP
      with hb | ⟨h1, h2, t, rfl⟩
    · exact (built ho (fun _ => hsh) hb hA).1
    · have := powerZero_parts hA; exact SettleEq.of_perm hK (h1.trans this.1.symm) (by rw [h2, this.2])
  | product c fs =>
    simp only [distributedPower, hrat, bind_value] at h
    obtain ⟨rs, hrs, h⟩ := bind_eq_value.1 h
    obtain ⟨-, Pa, hPa, ha⟩ := mkProduct_split h
    obtain ⟨Xs, hXs, hP'⟩ := bind_eq_value.1 hP; cases hP'
    obtain ⟨Rs, hRs, hPa'⟩ := bind_eq_value.1 hPa; cases hPa'
    rw [List.mapM_cons] at hRs
    obtain ⟨R0, hR0, hRs⟩ := bind_eq_value.1 hRs
    obtain ⟨Rs', hRs', hRs⟩ := bind_eq_value.1 hRs; cases hRs; cases hR0
    simp only [Term.nodeOk, canonicalProduct, Bool.and_eq_true, List.all_eq_true] at hok
    have pe : ∀ f ∈ fs, ∀ X r Rr, itemParts me q f = .value X → mergedPower o me f q = .value r →
        factorParts me 1 r = .value Rr →
        SettleEq o X Rr ∧ (Rr.coefficient ≠ 0 → ∀ x ∈ Rr.items, RootShape o me R x) := by
      intro f hf X r Rr hX hr hRr
      have hfo := hok.1.1.1 f hf
      have hfc := canonical_node hu (.tail _ (mem_nodesList.2 ⟨f, hf, mem_nodes_self f⟩))
      have hX' : factorParts me q f = .value X := by
        cases f <;> first | exact hX | simp [Term.factorOk] at hfo
      rcases mergedPower_parts hq2 hfo (List.all_eq_true.1 hfc.1 _ (mem_nodes_self _)) hr hX
        with hb | ⟨h1, h2, t, rfl⟩
      · exact built ho (fun _ => factorParts_shape (by omega) hfc (factorOk_value hfo) hX') hb hRr
      · have := powerZero_parts hRr
        exact ⟨SettleEq.of_perm hK (h1.trans this.1.symm) (by rw [h2, this.2]),
          fun _ x hx => by simp [this.2] at hx⟩
    have hF := SettleEq.foldl hK (forall₂_chain (mapM_value hXs) (mapM_value hrs)
      (mapM_value hRs') fun f hf X r Rr hX hr hRr => (pe f hf X r Rr hX hr hRr).1)
      (SettleEq.of_perm hK (p := ⟨c ^ q, [], []⟩)
        (q := ProductParts.unit.append ⟨(c ^ q) ^ (1 : ℤ), [], []⟩)
        (by simp [ProductParts.append, ProductParts.unit])
        (by simp [ProductParts.append, ProductParts.unit]))
    refine hF.trans (built (R := R) ho (fun hc0 x hx => ?_) ha hA).1
    obtain h0 | ⟨Rr, hRr, hx⟩ := (mem_items_foldl Rs' (ProductParts.unit.append _)).1 hx
    · simp [ProductParts.append, ProductParts.unit] at h0
    obtain ⟨r, hr, hRr'⟩ := (mapM_mem hRs').2 Rr hRr
    obtain ⟨f, hf, hr'⟩ := (mapM_mem hrs).2 r hr
    obtain ⟨X, -, hX⟩ := (mapM_mem hXs).1 f hf
    refine (pe f hf X r Rr hX hr' hRr').2 (fun e => hc0 ?_) x hx
    rw [foldl_append]
    exact mul_eq_zero_of_right _ (List.prod_eq_zero (by rw [← e]; exact List.mem_map_of_mem (.tail _ hRr)))

/-- The first round of the rounds of one item reduces it. -/
private theorem first_round {f : ℕ} {x : Term × ℤ} {ρ : ProductParts}
    (h : settleItems o me (f + 1) ⟨1, [x], []⟩ = .value ρ) : ∃ r, reduceItem me x = .value r := by
  rw [settleItems] at h
  obtain ⟨rs, hrs, -⟩ := bind_eq_value.1 h
  obtain ⟨r, -, hr⟩ := (mapM_mem hrs).1 x ((show mergeItems o [x] = [x] from rfl) ▸
    List.mem_singleton_self x)
  exact ⟨r, hr⟩

/-- The reduction of a power `k ≥ n` of a root of the degree `n`. -/
private theorem reduceItem_root {s u : Term} {n : ℕ} {k : ℤ} {r : ProductParts × List (Term × ℤ)}
    (hr : rootOf s = some (u, n)) (hk : (n : ℤ) ≤ k) (h : reduceItem me (s, k) = .value r) :
    ∃ P, factorParts me (k / n) u = .value P ∧
      r = (⟨P.coefficient, if k % n = 0 then [] else [(s, k % n)], P.ones⟩, P.items) := by
  obtain ⟨hn, hd, rest, rfl, -⟩ := rootOf_some hr
  rw [reduceItem] at h; unfold checkExponent at h; split at h; · cases h
  rw [ite_eq_right (by omega), ite_eq_right (by simp [Term.imaginaryUnit]), hr] at h
  dsimp only at h; rw [ite_eq_left hk] at h
  obtain ⟨P, hP, h⟩ := bind_eq_value.1 h
  exact ⟨P, hP, (Result.value.inj h).symm⟩

/-- The powers of roots of a literal degree: `(ⁿ√u)ᵏ = u ^ ⌊k/n⌋ (ⁿ√u) ^ (k mod n)` for
`k ≥ n`, when both sides succeed (`MergingAddsCoefficientsAndExponents`, last conjunct). -/
public theorem powersOfRoots (o : Orders) (me : ℕ) (R : RegistryRules) (ho : o.Total) :
    ∀ s u n k v w, Term.Canonical o me R s → rootOf s = some (u, n) → (n : ℤ) ≤ k →
      mkPower o me s k = .value v →
      (do
        let a ← mkPower o me u (k / n)
        let b ← mkPower o me s (k % n)
        mkProduct o me [a, b] : Result Term) = .value w → v = w := by
  intro s u n k v w hs hr hk hv hw
  have hK := keyCmp_total o ho
  obtain ⟨a, ha, hw⟩ := bind_eq_value.1 hw
  obtain ⟨b, hb, hw⟩ := bind_eq_value.1 hw
  have hn := (rootOf_some hr).1
  have hq : 1 ≤ k / n := Int.le_ediv_of_mul_le (by omega) (by omega)
  have hm := Int.emod_nonneg k (show (n : ℤ) ≠ 0 by omega)
  obtain ⟨huc, huv⟩ := (rootShape_root hs hr one_ne_zero).2 u n hr
  rcases root_pow hr (by omega) hv with ⟨h0, -⟩ | ⟨h1, -⟩ | ⟨-, hv⟩
  · omega
  · omega
  rw [buildProduct_eq] at hv; obtain ⟨ρ, hρ, rfl⟩ := map_eq_value.1 hv
  obtain ⟨r, hr1⟩ := first_round hρ
  obtain ⟨P, hP, rfl⟩ := reduceItem_root hr hk hr1
  obtain ⟨-, Pw, hPw, hw⟩ := mkProduct_split hw
  obtain ⟨Ps, hPs, hPw'⟩ := bind_eq_value.1 hPw; cases hPw'
  rcases mapM_value hPs with _ | @⟨_, A, _, _, hA, _ | @⟨_, B, _, _, hB, ⟨⟩⟩⟩
  have eB : SettleEq o ⟨1, if k % n = 0 then [] else [(s, k % n)], []⟩ B := by
    rcases root_pow hr hm hb with ⟨h0, rfl⟩ | ⟨h1, rfl⟩ | ⟨h2, hb'⟩
    · obtain ⟨e1, e2⟩ := powerZero_parts hB
      rw [ite_eq_left h0]; exact SettleEq.of_perm hK e1.symm (by rw [e2])
    · rw [ite_eq_right (by omega), h1]
      obtain ⟨-, hd, rest, rfl, -⟩ := rootOf_some hr
      simp [factorParts, itemParts] at hB; subst hB; exact SettleEq.of_perm hK rfl (.refl _)
    · rw [ite_eq_right (by omega)]
      exact (built ho (fun _ x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact rootShape_root hs hr (by omega))
        hb' hB).1
  have e := (SettleEq.reduce hK hr1 [] []).trans ((SettleEq.of_perm hK
    (q := P.append ⟨1, if k % n = 0 then [] else [(s, k % n)], []⟩) (by simp [ProductParts.append])
    (by simpa [ProductParts.append] using List.perm_append_comm)).trans
    (((pow_parts ho hq huc huv ha hP hA).append hK eB).trans (SettleEq.of_perm hK
      (q := [A, B].foldl ProductParts.append ProductParts.unit)
      (by simp [ProductParts.append, ProductParts.unit])
      (by simp [ProductParts.append, ProductParts.unit]))))
  rw [buildProduct_eq] at hw; obtain ⟨ρ', hρ', rfl⟩ := map_eq_value.1 hw
  obtain ⟨e1, e2⟩ := e.settle hK hρ hρ'
  refine finish_eq ho e1 e2 fun x => (settle_N (by simp; omega) hρ x).trans
    (Iff.trans ?_ (settled_N hPw hρ' x).symm)
  have h1 := (mkPower_bases huc ha).1 x
  have h2 := (mkPower_bases hs hb).1 x
  have hsk : itemFactor (s, k) = .power s k := by simp [itemFactor]; omega
  obtain ⟨-, hd, rest, rfl, -⟩ := rootOf_some hr
  simp only [List.map_cons, List.map_nil, hsk, List.append_nil, Term.negBasesList, List.mem_append,
    negBases_power_pos (show 0 ≤ k by omega), h1, h2, or_false,
    show ¬ k / n < 0 by omega, show ¬ k % n < 0 by omega, false_and]
  simp only [Term.negBases, Term.negBasesList, List.mem_append]; tauto

end Kalyx.Proofs.Terms.Grouping
