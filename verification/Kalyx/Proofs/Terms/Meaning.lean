module

public import Kalyx.Statements.Terms
public import Kalyx.Proofs.Terms.Basics
public import Kalyx.Proofs.Terms.Sums
public import Kalyx.Proofs.Terms.Bases
public import Kalyx.Proofs.Terms.Products

/-!
# The constructors keep the meaning of their inputs

Proves `ConstructorsKeepMeanings` from `CanonicalFormsAreClosedAndIdempotent`,
`ConstructorsKeepNegativeBases` and `CallsAreAtoms` (`constructorsKeepMeanings_of`).

A total valuation `tval`, with `0⁻¹ = 0` and the value 0 for a `piecewise` whose condition is
undefined, agrees with `Term.denote` wherever a term is defined. Every rewrite of a sum, a
product and a power keeps it: coefficients add, the exponents of one key add (`zpow_add'`, with
constants other than 0), powers of powers multiply, `i` has the period 4, roots follow
`Interp.RootLaw`, and witnesses and ones have the values 0 and 1. So the result of each
constructor has the total value of its input. Where the values inside the calls of `piecewise`
are defined, a strict node that is undefined makes the whole term undefined, and an undefined
canonical value has a base of a negative power whose value is 0. With the bases of the results
(the constructors keep `N`, and `Bases` gives the converse) this gives where the result is
defined. A call built by `mkCall` has the meaning of the call, by `RegistryRules.Keeps` and
`Interp.CondLaw`.
-/

namespace Kalyx.Proofs.Terms.Meaning

open Kalyx.Spec.Terms Kalyx.Spec.Fields Kalyx.Statements.Terms Kalyx.Proofs.Terms

variable {o : Orders} {me : ℕ} {R : RegistryRules} {I : Interp} {ρ : Assignment}

/-! ## The total value -/

mutual

/-- The total value: the meaning where defined, `0⁻¹ = 0`, 0 for a condition or an undefined `piecewise`. -/
private noncomputable def tval (I : Interp) (ρ : Assignment) : Term → ℂ
  | .number q => q
  | .constant c => c.denote I
  | .symbol s => ρ s
  | .call h args =>
    match h, args with
    | ⟨"piecewise", .formal⟩, [c, a, b] =>
      match Term.holds I ρ c with
      | some true => tval I ρ a
      | some false => tval I ρ b
      | none => 0
    | h, args => I.call h (tvalList I ρ args)
  | .power b k => tval I ρ b ^ k
  | .product c fs => c * (tvalList I ρ fs).prod
  | .sum c ms => c + tvalPairs I ρ ms
  | .condition .. => 0
  termination_by structural t => t

/-- The total values of a list of terms. -/
private noncomputable def tvalList (I : Interp) (ρ : Assignment) : List Term → List ℂ
  | [] => []
  | t :: ts => tval I ρ t :: tvalList I ρ ts
  termination_by structural ts => ts

/-- The total value of a list of monomials. -/
private noncomputable def tvalPairs (I : Interp) (ρ : Assignment) : List (ℚ × Term) → ℂ
  | [] => 0
  | (a, t) :: ms => a * tval I ρ t + tvalPairs I ρ ms
  termination_by structural ms => ms

end

/-- The total value of monomials, the sum of their values. -/
private noncomputable def mval (I : Interp) (ρ : Assignment) (ms : List (ℚ × Term)) : ℂ :=
  (ms.map fun m => (m.1 : ℂ) * tval I ρ m.2).sum

/-- The total values of a list are those of its terms. -/
@[simp] private theorem tvalList_eq (ts : List Term) : tvalList I ρ ts = ts.map (tval I ρ) := by
  induction ts with
  | nil => simp [tvalList]
  | cons t ts ih => simp [tvalList, ih]

/-- The total value of a list of monomials is `mval`. -/
private theorem tvalPairs_eq (ms : List (ℚ × Term)) : tvalPairs I ρ ms = mval I ρ ms := by
  induction ms with
  | nil => simp [tvalPairs, mval]
  | cons m ms ih => obtain ⟨a, t⟩ := m; simp [tvalPairs, ih, mval]

/-- The total value of a number. -/
@[simp] private theorem tval_number (q : ℚ) : tval I ρ (.number q) = q := by simp [tval]
/-- The total value of a power. -/
@[simp] private theorem tval_power (b : Term) (k : ℤ) :
    tval I ρ (.power b k) = tval I ρ b ^ k := by simp [tval]
/-- The total value of a product. -/
@[simp] private theorem tval_product (c : ℚ) (fs : List Term) :
    tval I ρ (.product c fs) = c * (fs.map (tval I ρ)).prod := by simp [tval]
/-- The total value of a sum. -/
@[simp] private theorem tval_sum (c : ℚ) (ms : List (ℚ × Term)) :
    tval I ρ (.sum c ms) = c + mval I ρ ms := by simp [tval, tvalPairs_eq]
/-- The total value of `i`. -/
@[simp] private theorem tval_I : tval I ρ Term.imaginaryUnit = Complex.I := by
  simp [tval, Term.imaginaryUnit, Constant.denote]

/-- The meaning of a call that is not a `piecewise` of three arguments. -/
private theorem denote_call_other (h : Head) (args : List Term)
    (hh : ∀ c a b, ¬(h = Head.piecewise ∧ args = [c, a, b])) :
    (Term.call h args).denote I ρ = (Term.denoteList I ρ args).map (I.call h) := by
  rw [Term.denote]; exact fun c a b h1 h2 => hh c a b ⟨h1, h2⟩

/-- The total value of such a call. -/
private theorem tval_call_other (h : Head) (args : List Term)
    (hh : ∀ c a b, ¬(h = Head.piecewise ∧ args = [c, a, b])) :
    tval I ρ (.call h args) = I.call h (args.map (tval I ρ)) := by
  rw [tval, tvalList_eq]; exact fun c a b h1 h2 => hh c a b ⟨h1, h2⟩

/-- A defined list, from the soundness of its terms: the total values, each term defined with its value. -/
private theorem denoteList_val : ∀ (ts : List Term),
    (∀ t ∈ ts, ∀ v, t.denote I ρ = some v → v = tval I ρ t) → ∀ vs, Term.denoteList I ρ ts = some vs →
      vs = ts.map (tval I ρ) ∧ ∀ t ∈ ts, t.denote I ρ = some (tval I ρ t)
  | [], _, vs, h => by simp only [Term.denoteList, Option.some.injEq] at h; simp [← h]
  | t :: ts, ih, vs, h => by
    simp only [Term.denoteList, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, ws, hws, rfl⟩ := h
    obtain rfl := ih t (.head _) v hv
    obtain ⟨rfl, h2⟩ := denoteList_val ts (fun t ht => ih t (.tail _ ht)) ws hws
    exact ⟨rfl, List.forall_mem_cons.2 ⟨hv, h2⟩⟩

/-- The value of defined monomials, from the soundness of their cores. -/
private theorem denotePairs_val : ∀ (ms : List (ℚ × Term)),
    (∀ m ∈ ms, ∀ v, m.2.denote I ρ = some v → v = tval I ρ m.2) →
    ∀ v, Term.denotePairs I ρ ms = some v → v = mval I ρ ms
  | [], _, v, h => by simp only [Term.denotePairs, Option.some.injEq] at h; simp [mval, h]
  | (a, t) :: ms, ih, v, h => by
    simp only [Term.denotePairs] at h
    obtain ⟨x, hx, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h2
    rw [ih (a, t) (by simp) x hx, denotePairs_val ms (fun m hm => ih m (by simp [hm])) w hw]
    simp [mval]

/-- Soundness: a defined term has its total value. -/
private theorem denote_val {t : Term} {v : ℂ} (h : t.denote I ρ = some v) : v = tval I ρ t := by
  induction t using term_induct generalizing v with
  | number | constant | symbol =>
    simp only [Term.denote, Option.some.injEq] at h; simp [tval, h]
  | call hd args ih =>
    by_cases hh : ∃ c a b, hd = Head.piecewise ∧ args = [c, a, b]
    · obtain ⟨c, a, b, rfl, rfl⟩ := hh
      simp only [Term.denote, Head.piecewise] at h
      simp only [tval, Head.piecewise]
      split at h
      · rename_i e; rw [e]; exact ih a (by simp) h
      · rename_i e; rw [e]; exact ih b (by simp) h
      · cases h
    · have hh' : ∀ c a b, ¬(hd = Head.piecewise ∧ args = [c, a, b]) :=
        fun c a b h' => hh ⟨c, a, b, h'⟩
      rw [denote_call_other hd args hh'] at h
      rw [tval_call_other hd args hh']
      obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [(denoteList_val args (fun a ha _ => ih a ha) vs hvs).1]
  | power b k ih =>
    simp only [Term.denote] at h
    obtain ⟨x, hx, hz⟩ := Option.bind_eq_some_iff.mp h
    rw [ih hx] at hz
    simp only [zpowMeaning] at hz
    split at hz
    · cases hz
    · simp only [Option.some.injEq] at hz; simp [hz]
  | product c fs ih =>
    simp only [Term.denote] at h
    obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [(denoteList_val fs (fun a ha _ => ih a ha) vs hvs).1, tval_product]
  | sum c ms ih =>
    simp only [Term.denote] at h
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [denotePairs_val ms (fun m hm _ => ih m hm) w hw, tval_sum]
  | condition => simp [Term.denote] at h

/-- A defined list: the total values, each term defined with its total value. -/
private theorem denoteList_some {ts : List Term} {vs : List ℂ}
    (h : Term.denoteList I ρ ts = some vs) :
    vs = ts.map (tval I ρ) ∧ ∀ t ∈ ts, t.denote I ρ = some (tval I ρ t) :=
  denoteList_val ts (fun _ _ _ => denote_val) vs h

/-- A list is undefined exactly where one of its terms is. -/
private theorem denoteList_none {ts : List Term} :
    Term.denoteList I ρ ts = none ↔ ∃ t ∈ ts, t.denote I ρ = none := by
  induction ts with
  | nil => simp [Term.denoteList]
  | cons t ts ih => cases ht : t.denote I ρ <;> simp [Term.denoteList, ht, ih]

/-- Monomials are undefined exactly where one of their cores is. -/
private theorem denotePairs_none {ms : List (ℚ × Term)} :
    Term.denotePairs I ρ ms = none ↔ ∃ m ∈ ms, m.2.denote I ρ = none := by
  induction ms with
  | nil => simp [Term.denotePairs]
  | cons m ms ih =>
    obtain ⟨a, t⟩ := m; cases ht : t.denote I ρ <;> simp [Term.denotePairs, ht, ih]

/-! ## Strictness and the zero bases -/

/-- `PiecewiseDefinedAt` of a term passes to a term whose nodes are nodes of it. -/
private theorem pda_of_mem {t a : Term} (h : PiecewiseDefinedAt I ρ [t])
    (hsub : ∀ x, x ∈ a.nodes → x ∈ t.nodes) : PiecewiseDefinedAt I ρ [a] := by
  intro u hu args s h1 h2 h3
  simp only [List.mem_singleton] at hu; subst hu
  exact h t (by simp) args s (hsub _ h1) h2 h3

/-- Strictness: an undefined value node makes the term undefined, given `PiecewiseDefinedAt`. -/
private theorem denote_none_of_mem (s : Term) (hs : s.isCondition = false)
    (hsn : s.denote I ρ = none) (t : Term) (hm : s ∈ t.nodes) (hpw : PiecewiseDefinedAt I ρ [t]) :
    t.denote I ρ = none := by
  induction t using term_induct with
  | number | constant | symbol =>
    simp only [Term.nodes, List.mem_singleton] at hm; subst hm; exact hsn
  | call h args ih =>
    simp only [Term.nodes, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact hsn
    by_cases hp : h = Head.piecewise
    · subst hp
      exact absurd hsn (hpw (Term.call Head.piecewise args) (List.mem_singleton_self _) args s
        (mem_nodes_self _) (by rw [Term.nodes]; exact List.mem_cons_of_mem _ hm) hs)
    obtain ⟨a, ha, hsa⟩ := mem_nodesList.mp hm
    have hsub : ∀ x, x ∈ a.nodes → x ∈ (Term.call h args).nodes :=
      fun x hx => by simp only [Term.nodes, List.mem_cons, mem_nodesList]; exact .inr ⟨a, ha, hx⟩
    rw [denote_call_other h args (fun _ _ _ e => hp e.1),
      denoteList_none.2 ⟨a, ha, ih a ha hsa (pda_of_mem hpw hsub)⟩]
    rfl
  | power b k ih =>
    simp only [Term.nodes, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact hsn
    have := ih hm (pda_of_mem hpw fun x hx => by simp [Term.nodes, hx])
    simp [Term.denote, this]
  | product c fs ih =>
    simp only [Term.nodes, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact hsn
    obtain ⟨a, ha, hsa⟩ := mem_nodesList.mp hm
    have := ih a ha hsa (pda_of_mem hpw fun _ => nodes_trans (mem_nodes_factor ha))
    simp [Term.denote, denoteList_none.2 ⟨a, ha, this⟩]
  | sum c ms ih =>
    simp only [Term.nodes, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact hsn
    obtain ⟨m, hm', hsm⟩ := mem_nodesPairs.mp hm
    have hsub : ∀ x, x ∈ m.2.nodes → x ∈ (Term.sum c ms).nodes :=
      fun x hx => by simp only [Term.nodes, List.mem_cons, mem_nodesPairs]; exact .inr ⟨m, hm', hx⟩
    simp [Term.denote, denotePairs_none.2 ⟨m, hm', ih m hm' hsm (pda_of_mem hpw hsub)⟩]
  | condition => simp [Term.denote]

/-- A base of `N` of value 0 makes the term undefined, given `PiecewiseDefinedAt`. -/
private theorem kill {u b : Term} (hp : PiecewiseDefinedAt I ρ [u]) (hb : b ∈ u.negBases)
    (hz : b.denote I ρ = some 0) : u.denote I ρ = none := by
  obtain ⟨k, hk, -, hn⟩ := mem_negBases.1 hb
  exact denote_none_of_mem (.power b k) rfl (by simp [Term.denote, hz, zpowMeaning, hk]) u hn hp

/-- A canonical value. -/
private def Op (o : Orders) (me : ℕ) (R : RegistryRules) (t : Term) : Prop :=
  Term.Canonical o me R t ∧ t.isCondition = false

/-- The node shape of a node of a canonical term. -/
private theorem nodeOk_of {t x : Term} (ht : Term.Canonical o me R t) (hx : x ∈ t.nodes) :
    x.nodeOk o me R = true := List.all_eq_true.1 ht.1 x hx

/-- An undefined canonical value has a base of `N` of value 0, given `PiecewiseDefinedAt`. -/
private theorem zero_base (hI : I.ConstantsNonzero) {t : Term} (ht : Op o me R t)
    (hp : PiecewiseDefinedAt I ρ [t]) (hn : t.denote I ρ = none) :
    ∃ b ∈ t.negBases, b.denote I ρ = some 0 := by
  obtain ⟨⟨hs, hv⟩, hc⟩ := ht
  suffices H : ∃ b k, Term.power b k ∈ t.nodes ∧ k < 0 ∧ b.isConstant = false ∧
      b.denote I ρ = some 0 by
    obtain ⟨b, k, h1, h2, h3, h4⟩ := H; exact ⟨b, mem_negBases.2 ⟨k, h2, h3, h1⟩, h4⟩
  have child : ∀ {t a : Term}, (∀ x, x ∈ a.nodes → x ∈ t.nodes) → t.shapeOk o me R = true →
      t.ConstantsValid → PiecewiseDefinedAt I ρ [t] →
      a.shapeOk o me R = true ∧ a.ConstantsValid ∧ PiecewiseDefinedAt I ρ [a] :=
    fun hsub hs hv hp => ⟨List.all_eq_true.2 fun x hx => List.all_eq_true.1 hs x (hsub x hx),
      fun c hc => hv c (hsub _ hc), pda_of_mem hp hsub⟩
  induction t using term_induct with
  | number | constant | symbol => simp [Term.denote] at hn
  | call h args ih =>
    by_cases hpw : h = Head.piecewise
    · subst hpw
      exact absurd hn (hp _ (List.mem_singleton_self _) args _ (mem_nodes_self _)
        (mem_nodes_self _) hc)
    rw [denote_call_other h args (fun _ _ _ e => hpw e.1), Option.map_eq_none_iff] at hn
    obtain ⟨a, ha, han⟩ := denoteList_none.1 hn
    have hok : (Term.call h args).nodeOk o me R = true := List.all_eq_true.1 hs _ (mem_nodes_self _)
    simp only [Term.nodeOk, canonicalCall, Bool.and_eq_true] at hok
    have hsub : ∀ x, x ∈ a.nodes → x ∈ (Term.call h args).nodes :=
      fun x hx => by simp only [Term.nodes, List.mem_cons, mem_nodesList]; exact .inr ⟨a, ha, hx⟩
    obtain ⟨hs', hv', hp'⟩ := child hsub hs hv hp
    obtain ⟨b, k, hbk, hk, hbc, hb0⟩ :=
      ih a ha hp' han (argsOkFrom_values hpw hok.1.1 a ha) hs' hv'
    exact ⟨b, k, hsub _ hbk, hk, hbc, hb0⟩
  | power b k ih =>
    have hok : (Term.power b k).nodeOk o me R = true := List.all_eq_true.1 hs _ (mem_nodes_self _)
    simp only [Term.nodeOk, canonicalPower, Bool.and_eq_true] at hok
    have hsub : ∀ x, x ∈ b.nodes → x ∈ (Term.power b k).nodes :=
      fun x hx => by simp [Term.nodes, hx]
    simp only [Term.denote, Option.bind_eq_none_iff] at hn
    cases hb : b.denote I ρ with
    | none =>
      obtain ⟨hs', hv', hp'⟩ := child hsub hs hv hp
      obtain ⟨c, j, hcj, hj, hcc, hc0⟩ := ih hp' hb (factorOk_value hok.1.1.1.1) hs' hv'
      exact ⟨c, j, hsub _ hcj, hj, hcc, hc0⟩
    | some x =>
      have hz := hn x hb
      simp only [zpowMeaning] at hz
      split at hz
      · rename_i hxk
        refine ⟨b, k, mem_nodes_self _, hxk.2, ?_, by rw [hb, hxk.1]⟩
        cases b with
        | constant c =>
          simp only [Term.denote, Option.some.injEq] at hb
          exact absurd (hb.trans hxk.1) (hI c (hv c (by simp [Term.nodes])))
        | _ => rfl
      · cases hz
  | product c fs ih =>
    have hok : (Term.product c fs).nodeOk o me R = true := List.all_eq_true.1 hs _ (mem_nodes_self _)
    simp only [Term.nodeOk, canonicalProduct, Bool.and_eq_true] at hok
    simp only [Term.denote, Option.map_eq_none_iff] at hn
    obtain ⟨a, ha, han⟩ := denoteList_none.1 hn
    obtain ⟨hs', hv', hp'⟩ := child (fun _ => nodes_trans (mem_nodes_factor ha)) hs hv hp
    obtain ⟨b, k, hbk, hk, hbc, hb0⟩ :=
      ih a ha hp' han (factorOk_value (List.all_eq_true.1 hok.1.1.1 a ha)) hs' hv'
    exact ⟨b, k, nodes_trans (mem_nodes_factor ha) hbk, hk, hbc, hb0⟩
  | sum c ms ih =>
    have hok : (Term.sum c ms).nodeOk o me R = true := List.all_eq_true.1 hs _ (mem_nodes_self _)
    simp only [Term.nodeOk, canonicalSum, Bool.and_eq_true] at hok
    simp only [Term.denote, Option.map_eq_none_iff] at hn
    obtain ⟨m, hm, hmn⟩ := denotePairs_none.1 hn
    have hsub : ∀ x, x ∈ m.2.nodes → x ∈ (Term.sum c ms).nodes :=
      fun x hx => by simp only [Term.nodes, List.mem_cons, mem_nodesPairs]; exact .inr ⟨m, hm, hx⟩
    obtain ⟨hs', hv', hp'⟩ := child hsub hs hv hp
    obtain ⟨b, k, hbk, hk, hbc, hb0⟩ :=
      ih m hm hp' hmn (coreOk_value (List.all_eq_true.1 hok.1.1.2 m hm)) hs' hv'
    exact ⟨b, k, hsub _ hbk, hk, hbc, hb0⟩
  | condition => simp [Term.isCondition] at hc

/-! ## Values of sums -/

/-- A scaled sum has the scaled value. -/
private theorem tval_scaleSum (a c : ℚ) (ms : List (ℚ × Term)) :
    tval I ρ (scaleSum a c ms) = a * tval I ρ (.sum c ms) := by
  simp only [scaleSum, tval_sum, mval, List.map_map, Function.comp_def, mul_add,
    ← List.sum_map_mul_left, Rat.cast_mul, mul_assoc]

/-- A sum is its content times its primitive part. -/
private theorem tval_prim (c : ℚ) (ms : List (ℚ × Term)) :
    tval I ρ (.sum c ms) = sumContent c ms * tval I ρ (primitivePart c ms) := by
  by_cases hs : sumContent c ms = 0
  · obtain ⟨rfl, h⟩ := sumContent_eq_zero hs
    rw [hs, tval_sum, mval, List.sum_eq_zero fun x hx => by
      obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx; simp [h m hm]]
    simp
  · rw [primitivePart, tval_scaleSum, ← mul_assoc, Rat.cast_inv,
      mul_inv_cancel₀ (by exact_mod_cast hs), one_mul]

/-- The core of the monomial of a product has the value of its factors. -/
private theorem tval_productCore (fs : List Term) :
    tval I ρ (productCore fs) = (fs.map (tval I ρ)).prod := by
  unfold productCore; split <;> simp

/-- Flattening keeps the total value of a sum. -/
private theorem tval_sumParts : ∀ ts : List Term,
    (ts.map (tval I ρ)).sum = (sumParts ts).1 + mval I ρ (sumParts ts).2
  | [] => by simp [sumParts, mval]
  | t :: ts => by
    have ih := tval_sumParts ts
    cases t <;> simp only [sumParts, List.map_cons, List.sum_cons, ih, tval_number, tval_sum,
      tval_product, mval, List.map_append, List.sum_append, tval_productCore] <;> push_cast <;> ring

/-- Merging keeps the total value of monomials. -/
private theorem mval_merge (o : Orders) (ms : List (ℚ × Term)) :
    mval I ρ (mergeMonomials o ms) = mval I ρ ms := by
  unfold mval mergeMonomials
  rw [mergeAdjacent_sum _ _ fun x y z h => ?_]
  · exact ((perm_sortBy _ ms).map _).sum_eq
  · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h; rename_i e; simp only [e]; push_cast; ring

/-- Removing the monomials with the coefficient 0 keeps the total value. -/
private theorem mval_filter (ms : List (ℚ × Term)) :
    mval I ρ (ms.filter fun m => decide (m.1 ≠ 0)) = mval I ρ ms := by
  induction ms with
  | nil => rfl
  | cons m ms ih => by_cases h : m.1 = 0 <;> simp_all [mval]

/-- Cancellation keeps the total value of monomials. -/
private theorem mval_cancel (o : Orders) (ms : List (ℚ × Term)) :
    mval I ρ (cancelMonomials o ms) = mval I ρ ms := by
  rw [Sums.cancelMonomials_eq]; split
  · exact mval_filter ms
  · rw [mval, ((perm_insertBy _ _ _).map _).sum_eq, ← mval_filter ms]; simp [mval]

/-- Assembly keeps the total value of monomials that read back, and gives a value. -/
private theorem tval_assembleSum (c : ℚ) (ms : List (ℚ × Term))
    (h : ∀ m ∈ ms, Sums.CoreShape m.2) :
    tval I ρ (assembleSum c ms) = c + mval I ρ ms ∧ (assembleSum c ms).isCondition = false := by
  match ms, h with
  | [], _ => simp [assembleSum, mval, Term.isCondition]
  | [(a, t)], h =>
    obtain ⟨hok, hpc⟩ := h (a, t) (by simp)
    simp only [assembleSum]
    split_ifs with hc ha
    · simp [hc, ha, mval, coreOk_value hok]
    · refine ⟨?_, rfl⟩; rw [tval_product, ← tval_productCore, hpc]; simp [hc, mval]
    · simp [mval, Term.isCondition]
  | _ :: _ :: _, _ => simp [assembleSum, Term.isCondition]

/-- A sum of canonical operands has the value of their sum, and is a value. -/
private theorem tval_mkSum (ho : o.Total) {ts : List Term} {u : Term}
    (hts : ∀ t ∈ ts, Term.Canonical o me R t) (h : mkSum o ts = .value u) :
    tval I ρ u = (ts.map (tval I ρ)).sum ∧ u.isCondition = false := by
  obtain ⟨hv, rfl⟩ := Sums.mkSum_eq_value.1 h
  obtain ⟨h1, h2⟩ := tval_assembleSum (I := I) (ρ := ρ) (sumParts ts).1
    (cancelMonomials o (mergeMonomials o (sumParts ts).2)) fun m hm => by
      rcases Sums.mem_cancelMonomials.1 hm with ⟨hm, -⟩ | ⟨-, rfl⟩
      · obtain ⟨m', hm', e⟩ := List.mem_map.1 ((mem_cores_mergeMonomials (termCmp_total o ho) _
          m.2).1 (List.mem_map_of_mem hm))
        exact e ▸ Sums.coreShape_sumParts hts hv m' hm'
      · exact Sums.coreShape_witnessCore _
  exact ⟨by rw [h1, mval_cancel, mval_merge, tval_sumParts], h2⟩

/-! ## Values of products -/

/-- The value of items: the product of the powers of their bases. -/
private noncomputable def ival (I : Interp) (ρ : Assignment) (items : List (Term × ℤ)) : ℂ :=
  (items.map fun x => tval I ρ x.1 ^ x.2).prod

/-- The value of the parts of a product. -/
private noncomputable def pval (I : Interp) (ρ : Assignment) (p : ProductParts) : ℂ :=
  p.coefficient * ival I ρ p.items

/-- The value of no items. -/
@[simp] private theorem ival_nil : ival I ρ [] = 1 := rfl
/-- The value of an item and more. -/
@[simp] private theorem ival_cons (x : Term × ℤ) (l : List (Term × ℤ)) :
    ival I ρ (x :: l) = tval I ρ x.1 ^ x.2 * ival I ρ l := by simp [ival]
/-- The value of two lists of items. -/
@[simp] private theorem ival_append (l l' : List (Term × ℤ)) :
    ival I ρ (l ++ l') = ival I ρ l * ival I ρ l' := by simp [ival]
/-- The value of a flattened list of items. -/
private theorem ival_flatten (L : List (List (Term × ℤ))) :
    ival I ρ L.flatten = (L.map (ival I ρ)).prod := by induction L <;> simp [*]

/-- A base of an item: a value with valid constants, whose radicand, if a root, is a canonical value. -/
private def Base (o : Orders) (me : ℕ) (R : RegistryRules) (b : Term) : Prop :=
  b.isCondition = false ∧ b.ConstantsValid ∧ ∀ u n, rootOf b = some (u, n) → Op o me R u

/-- Parts whose items have bases and whose ones have the value 1. -/
private def PartsOk (o : Orders) (me : ℕ) (R : RegistryRules) (I : Interp) (ρ : Assignment)
    (p : ProductParts) : Prop :=
  (∀ x ∈ p.items, Base o me R x.1) ∧ ∀ w ∈ p.ones, tval I ρ w = 1

/-- A canonical value is a base. -/
private theorem base_of_op {t : Term} (ht : Op o me R t) : Base o me R t :=
  ⟨ht.2, ht.1.2, fun _ _ hr => root_radicand ht.1 hr⟩

/-- The primitive part of a sum with valid constants is a base. -/
private theorem base_prim {c : ℚ} {ms : List (ℚ × Term)} (h : (Term.sum c ms).ConstantsValid) :
    Base o me R (primitivePart c ms) :=
  ⟨rfl, fun d hd => h d (by
    simp [primitivePart, scaleSum, Term.nodes, mem_nodesPairs] at hd ⊢
    obtain ⟨b, ⟨x, hx⟩, hb⟩ := hd; exact ⟨x, b, hx, hb⟩),
    fun _ _ e => by simp [primitivePart, scaleSum, rootOf] at e⟩

/-- The base of a canonical power is a canonical value. -/
private theorem op_powerBase {b : Term} {k : ℤ} (h : Term.Canonical o me R (.power b k)) :
    Op o me R b := by
  have := nodeOk_of h (mem_nodes_self _)
  simp only [Term.nodeOk, canonicalPower, Bool.and_eq_true] at this
  exact ⟨canonical_node h (by simp [Term.nodes, mem_nodes_self]), factorOk_value this.1.1.1.1⟩

/-- The values of a `mapM` of steps that keep values. -/
private theorem mapM_prod {α β : Type} {f : α → Result β} {P : α → Prop} {Q : β → Prop}
    {g : α → ℂ} {v : β → ℂ} (hf : ∀ a b, P a → f a = .value b → v b = g a ∧ Q b)
    {l : List α} {rs : List β} (h : l.mapM f = .value rs) (hl : ∀ a ∈ l, P a) :
    (rs.map v).prod = (l.map g).prod ∧ ∀ b ∈ rs, Q b := by
  have h2 := mapM_value h; clear h
  induction h2 with
  | nil => simp
  | cons hab _ ih =>
    obtain ⟨e, hq⟩ := hf _ _ (hl _ (.head _)) hab
    obtain ⟨ih1, ih2⟩ := ih fun a ha => hl a (.tail _ ha)
    exact ⟨by simp [e, ih1], List.forall_mem_cons.2 ⟨hq, ih2⟩⟩

/-- The value of a fold of parts, and its items and ones. -/
private theorem pval_foldl (rs : List ProductParts) (p : ProductParts) :
    pval I ρ (rs.foldl ProductParts.append p) = pval I ρ p * (rs.map (pval I ρ)).prod ∧
      (PartsOk o me R I ρ p → (∀ r ∈ rs, PartsOk o me R I ρ r) →
        PartsOk o me R I ρ (rs.foldl ProductParts.append p)) := by
  induction rs generalizing p with
  | nil => simp
  | cons r rs ih =>
    obtain ⟨ih1, ih2⟩ := ih (p.append r)
    refine ⟨by rw [List.foldl_cons, ih1]; simp only [pval, ProductParts.append, ival_append,
      Rat.cast_mul, List.map_cons, List.prod_cons]; ring, fun hp hr => ih2 ⟨?_, ?_⟩
        fun r' h => hr r' (.tail _ h)⟩
    · simp only [ProductParts.append, List.mem_append]
      rintro x (hx | hx); exacts [hp.1 x hx, (hr r (.head _)).1 x hx]
    · simp only [ProductParts.append, List.mem_append]
      rintro x (hx | hx); exacts [hp.2 x hx, (hr r (.head _)).2 x hx]

/-- The parts of a power of a canonical value that is not a product have its value. -/
private theorem itemParts_val {q : ℤ} {t : Term} {p : ProductParts} (ht : Op o me R t)
    (h : itemParts me q t = .value p) : pval I ρ p = tval I ρ t ^ q ∧ PartsOk o me R I ρ p := by
  obtain rfl := Products.itemParts_eq h
  cases t with
  | sum c ms =>
    refine ⟨?_, by simp [Products.uItem, PartsOk, base_prim ht.1.2]⟩
    rw [tval_prim]; simp [Products.uItem, pval, mul_zpow]
  | power b j =>
    simp only [Products.uItem]; split
    · subst j; simp [pval, PartsOk]
    · simp [pval, PartsOk, zpow_mul, base_of_op (op_powerBase ht.1)]
  | _ => simp [Products.uItem, pval, PartsOk, base_of_op ht]

/-- The parts of a power of a canonical value have its value. -/
private theorem factorParts_val {q : ℤ} {t : Term} {p : ProductParts} (ht : Op o me R t)
    (h : factorParts me q t = .value p) : pval I ρ p = tval I ρ t ^ q ∧ PartsOk o me R I ρ p := by
  cases t with
  | number r => simp only [factorParts, Result.value.injEq] at h; subst h; simp [pval, PartsOk]
  | product c fs =>
    have hok := nodeOk_of ht.1 (mem_nodes_self _)
    simp only [Term.nodeOk, canonicalProduct, Bool.and_eq_true, List.all_eq_true] at hok
    simp only [factorParts] at h
    obtain ⟨ps, hps, h⟩ := bind_eq_value.1 h
    simp only [pure_value, Result.value.injEq] at h; subst h
    obtain ⟨e, hok'⟩ := mapM_prod (P := Op o me R) (Q := PartsOk o me R I ρ)
      (g := fun f => tval I ρ f ^ q) (v := pval I ρ) (fun f r hf hr => itemParts_val hf hr) hps
      fun f hf => ⟨canonical_node ht.1 (mem_nodes_factor hf), factorOk_value (hok.1.1.1 f hf)⟩
    obtain ⟨e2, h2⟩ := pval_foldl (o := o) (me := me) (R := R) (I := I) (ρ := ρ) ps ⟨c ^ q, [], []⟩
    refine ⟨?_, h2 ⟨by simp, by simp⟩ hok'⟩
    rw [e2, e]; simp [pval, mul_zpow, List.prod_zpow, Function.comp_def]
  | _ => exact itemParts_val ht h

/-- Merging keeps a product of weights and a property that each join keeps. -/
private theorem mergeAdjacent_prod {α : Type} (join : α → α → Option α) (f : α → ℂ)
    (P : α → Prop) (hj : ∀ x y z, P x → P y → join x y = some z → f z = f x * f y ∧ P z) :
    ∀ l : List α, (∀ a ∈ l, P a) →
      ((mergeAdjacent join l).map f).prod = (l.map f).prod ∧ ∀ z ∈ mergeAdjacent join l, P z
  | [], _ => by simp [mergeAdjacent]
  | x :: rest, h => by
    have hP := fun l hl => mergeAdjacent_forall join P (fun x y z hz hx hy =>
      (hj x y z hx hy hz).2) l hl
    refine ⟨?_, hP _ h⟩
    have ih := (mergeAdjacent_prod join f P hj rest fun a ha => h a (.tail _ ha)).1
    have hr := hP rest fun a ha => h a (.tail _ ha)
    rcases mergeAdjacent_cons join x rest with e | ⟨y, more, z, hm, hz, e⟩ <;> rw [e]
    · simp [ih]
    · rw [hm] at ih hr; simp only [List.map_cons, List.prod_cons] at ih ⊢
      rw [(hj x y z (h x (.head _)) (hr y (.head _)) hz).1, mul_assoc, ih]

/-- Merging by key keeps the value of items with bases, and their bases. -/
private theorem mergeItems_val (hI : I.ConstantsNonzero) (items : List (Term × ℤ))
    (hb : ∀ x ∈ items, Base o me R x.1) :
    ival I ρ (mergeItems o items) = ival I ρ items ∧ ∀ x ∈ mergeItems o items, Base o me R x.1 := by
  have hj : ∀ x y z : Term × ℤ, Base o me R x.1 → Base o me R y.1 →
      (if Key.of x.1 x.2 = Key.of y.1 y.2 then some (x.1, x.2 + y.2) else none) = some z →
      tval I ρ z.1 ^ z.2 = tval I ρ x.1 ^ x.2 * tval I ρ y.1 ^ y.2 ∧ Base o me R z.1 := by
    rintro ⟨b, j⟩ ⟨b', k⟩ z hx - hz
    split at hz <;> simp only [Option.some.injEq, reduceCtorEq] at hz
    subst hz; rename_i hk
    simp only [Key.of, Key.mk.injEq] at hk
    obtain ⟨rfl, hk⟩ := hk
    refine ⟨zpow_add' ?_, hx⟩
    cases hc : b.isConstant
    · right; simp only [hc, Bool.not_false, Bool.and_true, decide_eq_decide] at hk
      by_cases hj : j < 0 <;> simp_all <;> omega
    · left; cases b <;> simp [Term.isConstant] at hc
      rename_i c; exact hI c (hx.2.1 c (by simp [Term.nodes]))
  have hp := perm_sortBy (fun x y : Term × ℤ => Key.cmp o (Key.of x.1 x.2) (Key.of y.1 y.2)) items
  obtain ⟨e, h⟩ := mergeAdjacent_prod _ (fun x : Term × ℤ => tval I ρ x.1 ^ x.2)
    (fun x => Base o me R x.1) hj _ fun x hx => hb x (hp.subset hx)
  exact ⟨e.trans (hp.map _).prod_eq, h⟩

/-- The root law for integer exponents `k ≥ n` of a degree `n ≥ 1`. -/
private theorem rootn_zpow (hR : I.RootLaw) (z : ℂ) (n : ℕ) (k : ℤ) (hn : 1 ≤ n)
    (hk : (n : ℤ) ≤ k) :
    I.call ⟨"rootn", .registered⟩ [z, n] ^ k =
      z ^ (k / n) * I.call ⟨"rootn", .registered⟩ [z, n] ^ (k % n) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m := ⟨k.toNat, by omega⟩
  rw [show ((m : ℤ) / (n : ℤ)) = ((m / n : ℕ) : ℤ) by push_cast; rfl,
    show ((m : ℤ) % (n : ℤ)) = ((m % n : ℕ) : ℤ) by push_cast; rfl]
  simp only [zpow_natCast]
  exact hR.2 z n m hn (by omega)

/-- The powers of a root of a literal degree reduce by the root law. -/
private theorem root_zpow (hR : I.RootLaw) {b u : Term} {n : ℕ} {k : ℤ}
    (hb : rootOf b = some (u, n)) (hk : (n : ℤ) ≤ k) :
    tval I ρ b ^ k = tval I ρ u ^ (k / n) * tval I ρ b ^ (k % n) := by
  have hnp : ∀ (h : Head) (args : List Term), h.callClass = .registered →
      ∀ c a b, ¬(h = Head.piecewise ∧ args = [c, a, b]) :=
    fun h _ hc _ _ _ e => by rw [e.1] at hc; cases hc
  unfold rootOf at hb
  split at hb
  · rename_i h u'
    split at hb
    · rename_i hh
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      subst hh
      have hc : tval I ρ (.call ⟨"sqrt", .registered⟩ [u']) =
          I.call ⟨"rootn", .registered⟩ [tval I ρ u', ((2 : ℕ) : ℂ)] := by
        rw [tval_call_other _ _ (hnp _ _ rfl), List.map_cons, List.map_nil, hR.1]; norm_num
      rw [hc]; exact rootn_zpow hR _ 2 k (by norm_num) hk
    · cases hb
  · rename_i h u' m
    split at hb
    · rename_i hh
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      obtain ⟨rfl, hd, hm⟩ := hh
      have hpos : (0 : ℤ) < m.num := Rat.num_pos.mpr (by linarith)
      have hmn : ((m.num.toNat : ℕ) : ℂ) = (m : ℂ) := by
        have h1 : ((m.num.toNat : ℕ) : ℤ) = m.num := Int.toNat_of_nonneg hpos.le
        have h2 : ((m.num : ℚ) : ℂ) = (m : ℂ) := by rw [Rat.coe_int_num_of_den_eq_one hd]
        rw [← h2, Rat.cast_intCast]; exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) h1
      have hc : tval I ρ (.call ⟨"rootn", .registered⟩ [u', .number m]) =
          I.call ⟨"rootn", .registered⟩ [tval I ρ u', ((m.num.toNat : ℕ) : ℂ)] := by
        rw [tval_call_other _ _ (hnp _ _ rfl), hmn]; simp
      rw [hc]; exact rootn_zpow hR _ _ k (by omega) hk
    · cases hb
  · cases hb

/-- `i ^ k` by `k` modulo 4. -/
private theorem I_zpow (k : ℤ) : Complex.I ^ k = (if k % 4 = 2 ∨ k % 4 = 3 then -1 else 1) *
    (if k % 4 = 1 ∨ k % 4 = 3 then Complex.I else 1) := by
  have hk : k = 4 * (k / 4) + k % 4 := by omega
  have hI : Complex.I ^ k = Complex.I ^ (k % 4) := by
    conv_lhs => rw [hk]
    rw [zpow_add₀ Complex.I_ne_zero, zpow_mul, show Complex.I ^ (4 : ℤ) = 1 by norm_num,
      one_zpow, one_mul]
  rw [hI]
  have h0 := Int.emod_nonneg k (by norm_num : (4 : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 4)
  interval_cases (k % 4) <;> simp [zpow_ofNat, pow_succ]

/-- A reduced item has the value of the item, in its parts and the items it sends back. -/
private theorem reduceItem_val (hR : I.RootLaw) {x : Term × ℤ}
    {r : ProductParts × List (Term × ℤ)} (hx : Base o me R x.1) (h : reduceItem me x = .value r) :
    pval I ρ r.1 * ival I ρ r.2 = tval I ρ x.1 ^ x.2 ∧ PartsOk o me R I ρ r.1 ∧
      ∀ y ∈ r.2, Base o me R y.1 := by
  obtain ⟨b, k⟩ := x
  simp only [reduceItem, checkExponent] at h
  split at h; · cases h
  split at h
  · simp only [Result.value.injEq] at h; subst h; rename_i hk; subst hk
    simp [pval, PartsOk, ProductParts.unit]
  split at h
  · simp only [Result.value.injEq] at h; subst h; rename_i hb; subst hb
    refine ⟨?_, ⟨by split_ifs <;> simp [hx], by simp⟩, by simp⟩
    simp only [pval, tval_I, I_zpow k]
    split_ifs <;> simp_all
  split at h
  · rename_i u n hr
    split at h
    · obtain ⟨p, hp, h⟩ := bind_eq_value.1 h
      simp only [pure_value, Result.value.injEq] at h; subst h
      obtain ⟨e, hok⟩ := factorParts_val (I := I) (ρ := ρ) (hx.2.2 u n hr) hp
      refine ⟨?_, ⟨by split_ifs <;> simp [hx], hok.2⟩, hok.1⟩
      rw [root_zpow hR hr ‹_›, ← e]
      split_ifs with h0 <;> simp [pval, h0]; ring
    · simp only [Result.value.injEq] at h; subst h; simp [pval, PartsOk, hx]
  · simp only [Result.value.injEq] at h; subst h; simp [pval, PartsOk, hx]

/-- The rounds of a product keep the value of its parts. -/
private theorem settleItems_val (hI : I.Lawful) : ∀ (fuel : ℕ) (p q : ProductParts),
    PartsOk o me R I ρ p → settleItems o me fuel p = .value q →
      pval I ρ q = pval I ρ p ∧ PartsOk o me R I ρ q
  | 0, _, _, _, h => by simp [settleItems] at h
  | fuel + 1, p, q, hp, h => by
    rw [settleItems] at h
    obtain ⟨rs, hrs, h⟩ := bind_eq_value.1 h
    obtain ⟨hm, hmb⟩ := mergeItems_val (o := o) (ρ := ρ) hI.2.2 p.items hp.1
    obtain ⟨e, hok⟩ := mapM_prod (P := fun x => Base o me R x.1)
      (Q := fun r => PartsOk o me R I ρ r.1 ∧ ∀ y ∈ r.2, Base o me R y.1)
      (g := fun x => tval I ρ x.1 ^ x.2) (v := fun r => pval I ρ r.1 * ival I ρ r.2)
      (fun x r hx hr => reduceItem_val hI.2.1 hx hr) hrs hmb
    have hf : rs.foldl (fun acc r => acc.append r.1) ⟨p.coefficient, [], p.ones⟩ =
        (rs.map Prod.fst).foldl ProductParts.append ⟨p.coefficient, [], p.ones⟩ :=
      (List.foldl_map ..).symm
    obtain ⟨e2, h2⟩ := pval_foldl (o := o) (me := me) (R := R) (I := I) (ρ := ρ)
      (rs.map Prod.fst) ⟨p.coefficient, [], p.ones⟩
    have key : pval I ρ (rs.foldl (fun acc r => acc.append r.1) ⟨p.coefficient, [], p.ones⟩) *
        ival I ρ (rs.map Prod.snd).flatten = pval I ρ p := by
      rw [hf, e2, ival_flatten, List.map_map, List.map_map, mul_assoc, ← List.prod_map_mul]
      simp only [Function.comp_def]; rw [e]; simp only [pval, ival_nil, mul_one]
      exact congrArg _ hm
    have hS := h2 ⟨by simp, hp.2⟩ fun r hr => by
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr; exact (hok r' hr').1
    rw [← hf] at hS
    have hB : ∀ y ∈ (rs.map Prod.snd).flatten, Base o me R y.1 := by
      simp only [List.mem_flatten, List.mem_map]
      rintro y ⟨_, ⟨r, hr, rfl⟩, hy⟩; exact (hok r hr).2 y hy
    dsimp only at h
    generalize rs.foldl (fun (acc : ProductParts) r => acc.append r.1) ⟨p.coefficient, [], p.ones⟩
      = S at h key hS
    split at h
    · rename_i hE; simp only [pure_value, Result.value.injEq] at h; subst h
      rw [List.isEmpty_iff.1 hE] at key; exact ⟨by simpa using key, hS⟩
    · obtain ⟨e3, h3⟩ := settleItems_val hI fuel ⟨S.coefficient, S.items ++ _, S.ones⟩ q ⟨by
        simp only [List.mem_append]; rintro y (hy | hy); exacts [hS.1 y hy, hB y hy], hS.2⟩ h
      exact ⟨by rw [e3, ← key]; simp only [pval, ival_append, mul_assoc], h3⟩

/-- Assembly keeps the value of a coefficient and factors, and gives a value. -/
private theorem tval_assembleProduct (c : ℚ) (L : List Term)
    (hL : ∀ f ∈ L, f.isCondition = false) :
    tval I ρ (assembleProduct c L) = c * (L.map (tval I ρ)).prod ∧
      (assembleProduct c L).isCondition = false := by
  match L, hL with
  | [], _ => simp [assembleProduct, Term.isCondition]
  | [f], hL =>
    simp only [assembleProduct]
    split
    · subst c; simp [hL f (.head _)]
    · split
      · exact ⟨by simp [tval_scaleSum], rfl⟩
      · simp [Term.isCondition]
  | _ :: _ :: _, _ => simp [assembleProduct, Term.isCondition]

/-- A built product has the value of its parts, and is a value. -/
private theorem buildProduct_val (hI : I.Lawful) {p : ProductParts} {u : Term}
    (hp : PartsOk o me R I ρ p) (h : buildProduct o me p = .value u) :
    tval I ρ u = pval I ρ p ∧ u.isCondition = false := by
  unfold buildProduct at h
  obtain ⟨p', hs, h⟩ := bind_eq_value.1 h
  obtain ⟨hv, hok⟩ := settleItems_val hI _ p p' hp hs
  rw [← hv]
  dsimp only at h
  split at h <;> simp only [pure_value, Result.value.injEq] at h <;> subst h
  · rename_i hc; unfold zeroWitness; split <;> simp [pval, hc, Term.isCondition]
  · have hL := perm_sortBy (fun f g : Term => Key.cmp o f.key g.key) (p'.items.map itemFactor ++
      (maxBases o (uncovered (Term.negBasesList p'.ones)
        (Term.negBasesList (p'.items.map itemFactor)))).map Term.oneOf)
    generalize sortBy _ _ = L at hL ⊢
    have hfac : ∀ x ∈ p'.items, tval I ρ (itemFactor x) = tval I ρ x.1 ^ x.2 ∧
        (itemFactor x).isCondition = false := fun x hx => by
      unfold itemFactor; split
      · rename_i h1; rw [h1, zpow_one]; exact ⟨rfl, (hok.1 x hx).1⟩
      · exact ⟨by simp, rfl⟩
    obtain ⟨e, hc⟩ := tval_assembleProduct (I := I) (ρ := ρ) p'.coefficient L fun f hf => by
      rcases List.mem_append.1 (hL.mem_iff.1 hf) with hf | hf <;>
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hf
      exacts [(hfac x hx).2, rfl]
    refine ⟨?_, hc⟩
    rw [e, (hL.map _).prod_eq, List.map_append, List.prod_append, List.map_map,
      List.map_congr_left (f := tval I ρ ∘ itemFactor) fun x hx => (hfac x hx).1]
    simp [pval, ival, Term.oneOf, Function.comp_def]

/-- A product of canonical operands has the value of their product, and is a value. -/
private theorem tval_mkProduct (hI : I.Lawful) {ts : List Term} {u : Term}
    (hts : ∀ t ∈ ts, Term.Canonical o me R t) (h : mkProduct o me ts = .value u) :
    tval I ρ u = (ts.map (tval I ρ)).prod ∧ u.isCondition = false := by
  have hv := (Products.mkProduct_split h).1
  unfold mkProduct at h; split at h; · cases h
  obtain ⟨p, hp, h⟩ := bind_eq_value.1 h
  unfold productParts at hp
  obtain ⟨ps, hps, hp⟩ := bind_eq_value.1 hp
  simp only [pure_value, Result.value.injEq] at hp; subst hp
  obtain ⟨e, hok⟩ := mapM_prod (P := Op o me R) (Q := PartsOk o me R I ρ) (g := tval I ρ)
    (v := pval I ρ) (fun t r ht hr => by simpa using factorParts_val (q := 1) ht hr) hps
    fun t ht => ⟨hts t ht, hv t ht⟩
  obtain ⟨e2, h2⟩ := pval_foldl (o := o) (me := me) (R := R) (I := I) (ρ := ρ) ps
    ProductParts.unit
  obtain ⟨v, hc⟩ := buildProduct_val hI (h2 ⟨by simp [ProductParts.unit],
    by simp [ProductParts.unit]⟩ hok) h
  exact ⟨by rw [v, e2, e]; simp [pval, ProductParts.unit], hc⟩

/-! ## Values of powers -/

/-- A power of a rational that is a value: the power, of no negative power of 0. -/
private theorem ratPowOp_value {r q : ℚ} {k : ℤ} (h : Result.ofOutcome (ratPowOp r k) = .value q) :
    q = r ^ k ∧ ¬(r = 0 ∧ k < 0) := by
  unfold ratPowOp ratPow at h; split at h <;> simp_all [FieldError.lift, Result.ofOutcome]

/-- The merges of powers of powers keep the value, down to a canonical value. -/
private theorem mergePowers_val (b : Term) : ∀ {k : ℤ} {c : Term} {j : ℤ}, Op o me R b →
    mergePowers me b k = .value (c, j) → tval I ρ c ^ j = tval I ρ b ^ k ∧ Op o me R c := by
  induction b using term_induct with
  | power d i ih =>
    intro k c j hb h
    rw [mergePowers] at h
    split at h
    · unfold checkExponent at h; split at h; · cases h
      obtain ⟨e, hc⟩ := ih (op_powerBase hb.1) h
      exact ⟨by rw [e, tval_power, zpow_mul], hc⟩
    · cases h; exact ⟨rfl, hb⟩
  | number | constant | symbol | call | product | sum | condition =>
    intro k c j hb h; simp only [mergePowers, Result.value.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, hb⟩

/-- The power 0 of a term has the value 1, and is a value. -/
private theorem tval_powerZero (o : Orders) (t : Term) :
    tval I ρ (powerZero o t) = 1 ∧ (powerZero o t).isCondition = false := by
  unfold powerZero; split <;> simp [Term.oneOf, Term.isCondition, Function.comp_def]

/-- A merged power of a canonical value has the value of the power, and is a value. -/
private theorem mergedPower_val (hI : I.Lawful) {b u : Term} {k : ℤ} (hb : Op o me R b)
    (h : mergedPower o me b k = .value u) : tval I ρ u = tval I ρ b ^ k ∧ u.isCondition = false := by
  obtain ⟨⟨c, j⟩, hm, h⟩ := bind_eq_value.1 h
  obtain ⟨e, hc⟩ := mergePowers_val (I := I) (ρ := ρ) b hb hm
  rw [← e]
  dsimp only at h
  split at h
  · cases h; subst j; simp [hc.2]
  split at h
  · cases h; subst j; simpa using tval_powerZero o c
  · obtain ⟨v, hv⟩ := buildProduct_val (R := R) (ρ := ρ) hI ⟨by simp [base_of_op hc], by simp⟩ h
    exact ⟨by simp [v, pval], hv⟩

/-- A power of a factor is its merged power. -/
private theorem mkPower_factor {f : Term} {k : ℤ} (hf : f.factorOk = true) (h0 : k ≠ 0)
    (h1 : k ≠ 1) (hk : ¬exponentBound me < k.natAbs) : mkPower o me f k = mergedPower o me f k := by
  cases f with
  | sum c ms =>
    simp only [Term.factorOk, beq_iff_eq] at hf
    simp [mkPower, checkExponent, hk, Term.isCondition, h0, h1, distributedPower, hf, ratPowOp,
      ratPow, FieldError.lift, Result.ofOutcome, mergedPower, mergePowers, primitivePart, scaleSum]
  | number | product | condition => simp [Term.factorOk] at hf
  | _ => simp [mkPower, checkExponent, hk, Term.isCondition, h0, h1, distributedPower]

/-- A power of a canonical base has the value of the power; the base and the power are values. -/
private theorem tval_mkPower (hI : I.Lawful) {k : ℤ}
    (hP : ∀ f r, Term.Canonical o me R f → mkPower o me f k = .value r → Term.Canonical o me R r)
    {b u : Term} (hb : Term.Canonical o me R b) (h : mkPower o me b k = .value u) :
    tval I ρ u = tval I ρ b ^ k ∧ u.isCondition = false ∧ b.isCondition = false := by
  obtain ⟨hk, hbc, hcase⟩ := Bases.mkPower_cases h
  refine (fun H : _ ∧ _ => ⟨H.1, H.2, hbc⟩) ?_
  rcases hcase with ⟨r, q, rfl, rfl, hq⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h1, h0, -, h⟩
  · obtain ⟨rfl, -⟩ := ratPowOp_value hq; simp [Term.isCondition]
  · simp [hbc]
  · simpa using tval_powerZero o b
  cases b with
  | product c fs =>
    simp only [distributedPower] at h
    obtain ⟨ck, hck, h⟩ := bind_eq_value.1 h
    obtain ⟨rs, hrs, h⟩ := bind_eq_value.1 h
    obtain ⟨rfl, -⟩ := ratPowOp_value hck
    have hok := nodeOk_of hb (mem_nodes_self _)
    simp only [Term.nodeOk, canonicalProduct, Bool.and_eq_true, List.all_eq_true] at hok
    obtain ⟨e, hcan⟩ := mapM_prod (P := fun f => f ∈ fs) (Q := Term.Canonical o me R)
      (g := fun f => tval I ρ f ^ k) (v := tval I ρ) (fun f r hf hr => by
        have hfc := canonical_node hb (mem_nodes_factor hf)
        have hfo := hok.1.1.1 f hf
        exact ⟨(mergedPower_val hI ⟨hfc, factorOk_value hfo⟩ hr).1,
          hP f r hfc (by rw [mkPower_factor hfo h0 h1 hk]; exact hr)⟩) hrs fun _ h => h
    obtain ⟨v, hv⟩ := tval_mkProduct (ρ := ρ) hI (List.forall_mem_cons.2 ⟨canonical_number _, hcan⟩) h
    exact ⟨by rw [v]; simp [e, mul_zpow, List.prod_zpow, Function.comp_def], hv⟩
  | sum c ms =>
    simp only [distributedPower] at h
    obtain ⟨ck, hck, h⟩ := bind_eq_value.1 h
    obtain ⟨rfl, -⟩ := ratPowOp_value hck
    obtain ⟨v, hv⟩ := buildProduct_val (R := R) (ρ := ρ) hI ⟨by simp [base_prim hb.2], by simp⟩ h
    exact ⟨by rw [v, tval_prim]; simp [pval, mul_zpow], hv⟩
  | condition => simp [Term.isCondition] at hbc
  | _ => exact mergedPower_val hI ⟨hb, hbc⟩ h

/-! ## Bases that a negative power introduces -/

/-- A scaled sum is defined where the sum is, with the scaled value. -/
private theorem denote_scale (a c : ℚ) (ms : List (ℚ × Term)) :
    (scaleSum a c ms).denote I ρ = ((Term.sum c ms).denote I ρ).map ((a : ℂ) * ·) := by
  have : ∀ ms : List (ℚ × Term), Term.denotePairs I ρ (ms.map fun m => (a * m.1, m.2)) =
      (Term.denotePairs I ρ ms).map ((a : ℂ) * ·) := by
    intro ms; induction ms with
    | nil => simp [Term.denotePairs]
    | cons m ms ih =>
      obtain ⟨b, t⟩ := m
      simp only [List.map_cons, Term.denotePairs, ih]
      cases t.denote I ρ <;> cases Term.denotePairs I ρ ms <;> simp [mul_add, mul_assoc]
  simp only [scaleSum, Term.denote, this]; cases Term.denotePairs I ρ ms <;> simp; ring

/-- A factor of value 0 that is not a number introduces a base of value 0. -/
private theorem zero_introducedBase (hI : I.ConstantsNonzero) {f : Term} (hf : f.ConstantsValid)
    (hn : ∀ r, f ≠ .number r) (hz : f.denote I ρ = some 0) :
    ∃ c ∈ f.introducedBase, c.denote I ρ = some 0 := by
  cases f with
  | number r => exact absurd rfl (hn r)
  | constant c =>
    simp only [Term.denote, Option.some.injEq] at hz
    exact absurd hz (hI c (hf c (by simp [Term.nodes])))
  | power d j =>
    simp only [Term.denote, Option.bind_eq_some_iff] at hz
    obtain ⟨x, hx, hz⟩ := hz
    simp only [zpowMeaning] at hz
    split at hz; · cases hz
    rename_i hxj
    simp only [Option.some.injEq] at hz
    have hj : j ≠ 0 := by rintro rfl; simp at hz
    obtain rfl := (zpow_eq_zero_iff hj).1 hz
    have hj' : 0 < j := by simp at hxj; omega
    cases hd : d.isConstant
    · exact ⟨d, by simp [Term.introducedBase, hd, hj, not_lt.2 hj'.le], hx⟩
    · cases d <;> simp [Term.isConstant] at hd
      rename_i c; simp only [Term.denote, Option.some.injEq] at hx
      exact absurd hx (hI c (hf c (by simp [Term.nodes])))
  | sum c ms =>
    exact ⟨primitivePart c ms, by simp [Term.introducedBase], by
      rw [primitivePart, denote_scale, hz]; simp⟩
  | condition => simp [Term.denote] at hz
  | symbol | call | product => exact ⟨_, by simp [Term.introducedBase], hz⟩

/-- Where a negative power of a canonical base is a value and the base is 0, an introduced base is 0. -/
private theorem exists_zero_introduced (hI : I.ConstantsNonzero) {b u : Term} {k : ℤ}
    (hb : Term.Canonical o me R b) (hk : k < 0) (h : mkPower o me b k = .value u)
    (hz : b.denote I ρ = some 0) : ∃ c ∈ b.introducedBases, c.denote I ρ = some 0 := by
  obtain ⟨-, -, hcase⟩ := Bases.mkPower_cases h
  rcases hcase with ⟨r, q, rfl, -, hq⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, -, hn, h⟩
  · simp only [Term.denote, Option.some.injEq, Rat.cast_eq_zero] at hz
    exact absurd ⟨hz, hk⟩ (ratPowOp_value hq).2
  · omega
  · omega
  cases b with
  | product c fs =>
    simp only [distributedPower] at h
    obtain ⟨ck, hck, -⟩ := bind_eq_value.1 h
    have hc0 : c ≠ 0 := fun e => (ratPowOp_value hck).2 ⟨e, hk⟩
    simp only [Term.denote, Option.map_eq_some_iff] at hz
    obtain ⟨vs, hvs, hz⟩ := hz
    obtain ⟨rfl, hall⟩ := denoteList_some hvs
    have h0 : (0 : ℂ) ∈ fs.map (tval I ρ) := by
      rw [← List.prod_eq_zero_iff]; simpa [hc0] using hz
    obtain ⟨f, hf, hf0⟩ := List.mem_map.1 h0
    have hok := nodeOk_of hb (mem_nodes_self _)
    simp only [Term.nodeOk, canonicalProduct, Bool.and_eq_true, List.all_eq_true] at hok
    obtain ⟨d, hd, hd0⟩ := zero_introducedBase hI (canonical_node hb (mem_nodes_factor hf)).2
      (fun r e => by have := hok.1.1.1 f hf; subst e; simp [Term.factorOk] at this)
      (by rw [hall f hf, hf0])
    exact ⟨d, List.mem_flatMap.2 ⟨f, hf, hd⟩, hd0⟩
  | _ => exact zero_introducedBase hI hb.2 hn hz

/-- A base of value 0 that a factor introduces makes the factor undefined or 0. -/
private theorem zero_of_introducedBase {f c : Term} (hc : c ∈ f.introducedBase)
    (hz : c.denote I ρ = some 0) : f.denote I ρ = none ∨ f.denote I ρ = some 0 := by
  cases f with
  | number | constant | condition => simp [Term.introducedBase] at hc
  | power d j =>
    simp only [Term.introducedBase] at hc
    split_ifs at hc with h1 h2
    · rw [List.mem_singleton] at hc; subst hc; exact .inr hz
    · simp at hc
    · rw [List.mem_singleton] at hc; subst hc
      have : j ≠ 0 := fun e => h2 (.inl e)
      right; simp [Term.denote, hz, zpowMeaning, h1, zero_zpow _ this]
  | sum a ms =>
    simp only [Term.introducedBase, List.mem_singleton] at hc; subst hc
    cases hs : (Term.sum a ms).denote I ρ with
    | none => exact .inl rfl
    | some w => exact .inr (by rw [denote_val hs, tval_prim, ← denote_val hz, mul_zero])
  | symbol | call | product =>
    simp only [Term.introducedBase, List.mem_singleton] at hc; subst hc; exact .inr hz

/-- A base of value 0 that a power introduces makes its base undefined or 0. -/
private theorem zero_of_introduced {b c : Term} (hc : c ∈ b.introducedBases)
    (hz : c.denote I ρ = some 0) : b.denote I ρ = none ∨ b.denote I ρ = some 0 := by
  cases b with
  | product a fs =>
    obtain ⟨f, hf, hc⟩ := List.mem_flatMap.1 hc
    cases hl : Term.denoteList I ρ fs with
    | none => exact .inl (by simp [Term.denote, hl])
    | some vs =>
      obtain ⟨rfl, hall⟩ := denoteList_some hl
      rcases zero_of_introducedBase hc hz with h | h <;> rw [hall f hf] at h
      · cases h
      · right; simp only [Term.denote, hl, Option.map_some, Option.some.injEq]
        rw [List.prod_eq_zero (List.mem_map.2 ⟨f, hf, Option.some.inj h⟩), mul_zero]
  | _ => exact zero_of_introducedBase hc hz

/-! ## Where the results are defined -/

/-- `PiecewiseDefinedAt` passes to a term whose calls are calls of the terms. -/
private theorem pda_of_callsWithin {u : Term} {ts : List Term} (hw : CallsWithin u ts)
    (h : PiecewiseDefinedAt I ρ ts) : PiecewiseDefinedAt I ρ [u] := by
  intro t ht args s hc hs hsc
  rw [List.mem_singleton] at ht; subst ht
  obtain ⟨t', ht', hc'⟩ := hw _ _ hc
  exact h t' ht' args s hc' hs hsc

/-- The values inside the calls of `piecewise` of terms without them are defined. -/
private theorem pda_of_np {ts : List Term} (h : NoPiecewise ts) : PiecewiseDefinedAt I ρ ts :=
  fun t ht args _ hc => absurd hc (h t ht args)

/-- `MeaningKept` from total values, kept bases, calls, and introduced bases `E`, of value 0 where `Zc`. -/
private theorem meaningKept_gen (hI : I.ConstantsNonzero) {ts : List Term} {u : Term}
    {f : Assignment → Option ℂ} (F : Assignment → ℂ) (E : Term → Prop) (Zc : Assignment → Prop)
    (hts : ∀ t ∈ ts, Op o me R t) (hu : Op o me R u) (hk : BasesKept ts u)
    (hE0 : ∀ c, E c → c ∈ u.negBases) (hN : ∀ b ∈ u.negBases, b ∈ Term.negBasesList ts ∨ E b)
    (hw : CallsWithin u ts) (hE1 : ∀ ρ, Zc ρ → ∃ c, E c ∧ c.denote I ρ = some 0)
    (hE2 : ∀ ρ c, E c → c.denote I ρ = some 0 → (∃ t ∈ ts, t.denote I ρ = none) ∨ Zc ρ)
    (hA : ∀ ρ, tval I ρ u = F ρ) (hF : ∀ ρ w, f ρ = some w → w = F ρ)
    (hD : ∀ ρ, f ρ = none ↔ (∃ t ∈ ts, t.denote I ρ = none) ∨ Zc ρ) : MeaningKept I ts u f := by
  have hB : ∀ ρ, PiecewiseDefinedAt I ρ ts → ∀ v, u.denote I ρ = some v → f ρ = some v := by
    intro ρ hp v hv
    have hpu := pda_of_callsWithin hw hp
    cases hf : f ρ with
    | some w => rw [hF ρ w hf, ← hA, ← denote_val hv]
    | none =>
      exfalso
      rcases (hD ρ).1 hf with ⟨t, ht, htn⟩ | hz
      · obtain ⟨b, hb, hb0⟩ := zero_base hI (hts t ht) (pda_of_callsWithin (fun _ _ hc => ⟨t, ht, hc⟩) hp) htn
        rw [kill hpu (hk b (mem_negBasesList.2 ⟨t, ht, hb⟩)) hb0] at hv; cases hv
      · obtain ⟨c, hc, hc0⟩ := hE1 ρ hz
        rw [kill hpu (hE0 c hc) hc0] at hv; cases hv
  refine ⟨fun hnp ρ => ?_, fun ρ v w hv hw' => (denote_val hv).trans ((hA ρ).trans
    (hF ρ w hw').symm), hB⟩
  cases hv : u.denote I ρ with
  | some v => exact (hB ρ (pda_of_np hnp) v hv).symm
  | none =>
    have hnu : NoPiecewise [u] := fun t ht args hc => by
      rw [List.mem_singleton] at ht; subst ht
      obtain ⟨t', ht', hc'⟩ := hw _ _ hc; exact hnp t' ht' args hc'
    obtain ⟨b, hb, hb0⟩ := zero_base hI hu (pda_of_np hnu) hv
    refine ((hD ρ).2 ?_).symm
    rcases hN b hb with hb | hb
    · obtain ⟨t, ht, hbt⟩ := mem_negBasesList.1 hb
      exact .inl ⟨t, ht, kill (pda_of_np fun _ h => List.mem_singleton.1 h ▸ hnp t ht) hbt hb0⟩
    · exact hE2 ρ b hb hb0

/-! ## The constructors -/

/-- Proves `ConstructorsKeepMeanings` from the closure of the canonical forms, the bases of
negative powers that the constructors keep, and calls as atoms. -/
public theorem constructorsKeepMeanings_of (hClosed : CanonicalFormsAreClosedAndIdempotent)
    (hBases : ConstructorsKeepNegativeBases) (hCalls : CallsAreAtoms) : ConstructorsKeepMeanings := by
  intro o me R I ho hR hK hI
  dsimp only
  obtain ⟨c1, c2, c3, c4, c5, c6, -⟩ := hClosed o me R ho hR
  obtain ⟨b1, b2, b3, b4, b5, b6, -, b8, b9, -⟩ := hBases o me R ho hR
  obtain ⟨w1, w2, w3, -⟩ := hCalls o me R ho hR
  have can : ∀ {r : Result Term} {u : Term}, CanonicalResult (Term.Canonical o me R) r →
      r = .value u → Term.Canonical o me R u := by rintro r u hc rfl; exact hc
  have hP : ∀ {k : ℤ} f r, Term.Canonical o me R f → mkPower o me f k = .value r →
      Term.Canonical o me R r := fun f r hf h => can (c3 f _ hf) h
  have hI0 := hI.2.2
  refine ⟨fun ts u hts h => ?_, fun ts u hts h => ?_, fun b k u hb h => ?_,
    fun t u ht h => ?_, fun a b u ha hb h => ?_, fun a b u ha hb h => ?_,
    fun hd args u _ h ρ => ?_⟩
  · have hv := (Sums.mkSum_eq_value.1 h).1
    refine meaningKept_gen hI0 (fun ρ => (ts.map (tval I ρ)).sum) (fun _ => False)
      (fun _ => False) (fun t ht => ⟨hts t ht, hv t ht⟩)
      ⟨can (c1 ts hts) h, (tval_mkSum (I := I) (ρ := fun _ => 0) ho hts h).2⟩ (b1 ts u hts h)
      (fun _ => False.elim) (fun x hx => .inl (((Bases.mkSum_bases h).1 x).1 hx)) (w1 ts u hts h)
      (fun _ => False.elim) (fun _ _ => False.elim) (fun ρ => (tval_mkSum ho hts h).1)
      (fun ρ w hw => ?_) (fun ρ => by simp [denoteList_none])
    obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.1 hw; rw [(denoteList_some hvs).1]
  · have hv := (Products.mkProduct_split h).1
    refine meaningKept_gen hI0 (fun ρ => (ts.map (tval I ρ)).prod) (fun _ => False)
      (fun _ => False) (fun t ht => ⟨hts t ht, hv t ht⟩)
      ⟨can (c2 ts hts) h, (tval_mkProduct (ρ := fun _ => 0) hI hts h).2⟩ (b2 ts u hts h)
      (fun _ => False.elim) (fun x hx => .inl (((Bases.mkProduct_bases h).1 x).1 hx))
      (w2 ts u hts h) (fun _ => False.elim) (fun _ _ => False.elim)
      (fun ρ => (tval_mkProduct hI hts h).1) (fun ρ w hw => ?_) (fun ρ => by simp [denoteList_none])
    obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.1 hw; rw [(denoteList_some hvs).1]
  · have hT := fun ρ => tval_mkPower (ρ := ρ) hI hP hb h
    refine meaningKept_gen hI0 (fun ρ => tval I ρ b ^ k) (fun c => k < 0 ∧ c ∈ b.introducedBases)
      (fun ρ => k < 0 ∧ b.denote I ρ = some 0) (by simpa using ⟨hb, (hT fun _ => 0).2.2⟩)
      ⟨can (c3 b k hb) h, (hT fun _ => 0).2.1⟩ (b3 b k u hb h)
      (fun c hc => b8 b k u hb hc.1 h c hc.2)
      (fun x hx => by simpa [Term.negBasesList] using ((Bases.mkPower_bases hb h).1 x).1 hx)
      (w3 b k u hb h) (fun ρ hz => let ⟨c, hc, hc0⟩ := exists_zero_introduced hI0 hb hz.1 h hz.2
        ⟨c, ⟨hz.1, hc⟩, hc0⟩)
      (fun ρ c hc hz => (zero_of_introduced hc.2 hz).imp (fun hn => ⟨b, by simp, hn⟩)
        fun h0 => ⟨hc.1, h0⟩) (fun ρ => (hT ρ).1) (fun ρ w hw => ?_) (fun ρ => ?_)
    · obtain ⟨x, hx, hw⟩ := Option.bind_eq_some_iff.1 hw
      simp only [zpowMeaning] at hw; split at hw; · cases hw
      cases hw; rw [denote_val hx]
    · cases hx : b.denote I ρ <;> simp [hx, zpowMeaning, and_comm]
  · have h' : mkProduct o me [.number (-1), t] = .value u := h
    have hv := (Products.mkProduct_split h').1
    have hts : ∀ x ∈ [Term.number (-1), t], Term.Canonical o me R x :=
      List.forall_mem_cons.2 ⟨canonical_number _, by simpa using ht⟩
    refine meaningKept_gen hI0 (fun ρ => -tval I ρ t) (fun _ => False) (fun _ => False)
      (by simpa using ⟨ht, hv t (by simp)⟩)
      ⟨can (c4 t ht) h, (tval_mkProduct (ρ := fun _ => 0) hI hts h').2⟩ (b4 t u ht h)
      (fun _ => False.elim)
      (fun x hx => .inl (by simpa [Term.negBasesList] using ((Bases.mkNegate_bases h).1 x).1 hx))
      (callsWithin_of_nodesFrom (Bases.mkNegate_bases h).2) (fun _ => False.elim)
      (fun _ _ => False.elim) (fun ρ => by simpa using (tval_mkProduct hI hts h').1)
      (fun ρ w hw => ?_) (fun ρ => by simp)
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hw; rw [denote_val hx]
  · obtain ⟨nb, hn, hs⟩ := bind_eq_value.1 h
    have hn' : mkProduct o me [.number (-1), b] = .value nb := hn
    have hv := (Sums.mkSum_eq_value.1 hs).1
    have hbv := (Products.mkProduct_split hn').1
    have hts2 : ∀ x ∈ [a, nb], Term.Canonical o me R x := by simpa using ⟨ha, can (c4 b hb) hn⟩
    have hts1 : ∀ x ∈ [Term.number (-1), b], Term.Canonical o me R x :=
      List.forall_mem_cons.2 ⟨canonical_number _, by simpa using hb⟩
    refine meaningKept_gen hI0 (fun ρ => tval I ρ a - tval I ρ b) (fun _ => False)
      (fun _ => False) (by simpa using ⟨⟨ha, hv a (by simp)⟩, hb, hbv b (by simp)⟩)
      ⟨can (c5 a b ha hb) h, (tval_mkSum (I := I) (ρ := fun _ => 0) ho hts2 hs).2⟩ (b5 a b u ha hb h)
      (fun _ => False.elim) (fun x hx => .inl (((Bases.mkSubtract_bases h).1 x).1 hx))
      (callsWithin_of_nodesFrom (Bases.mkSubtract_bases h).2) (fun _ => False.elim)
      (fun _ _ => False.elim) (fun ρ => ?_) (fun ρ w hw => ?_) (fun ρ => ?_)
    · rw [(tval_mkSum ho hts2 hs).1]; simp [(tval_mkProduct hI hts1 hn').1, sub_eq_add_neg]
    · obtain ⟨x, hx, hw⟩ := Option.bind_eq_some_iff.1 hw
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hw
      rw [denote_val hx, denote_val hy]
    · cases hx : a.denote I ρ <;> cases hy : b.denote I ρ <;> simp [hx, hy]
  · obtain ⟨r, hr, hp⟩ := bind_eq_value.1 h
    have hT := fun ρ => tval_mkPower (ρ := ρ) hI hP hb hr
    have hav := (Products.mkProduct_split hp).1
    have hts : ∀ x ∈ [a, r], Term.Canonical o me R x := by simpa using ⟨ha, can (c3 b (-1) hb) hr⟩
    refine meaningKept_gen hI0 (fun ρ => tval I ρ a * tval I ρ b ^ (-1 : ℤ))
      (fun c => c ∈ b.introducedBases) (fun ρ => b.denote I ρ = some 0)
      (by simpa using ⟨⟨ha, hav a (by simp)⟩, hb, (hT fun _ => 0).2.2⟩)
      ⟨can (c6 a b ha hb) h, (tval_mkProduct (ρ := fun _ => 0) hI hts hp).2⟩ (b6 a b u ha hb h)
      (fun c hc => b9 a b u ha hb h c hc) (fun x hx => ((Bases.mkDivide_bases hb h).1 x).1 hx)
      (callsWithin_of_nodesFrom (Bases.mkDivide_bases hb h).2)
      (fun ρ hz => exists_zero_introduced hI0 hb (by norm_num) hr hz)
      (fun ρ c hc hz => (zero_of_introduced hc hz).imp_left fun hn => ⟨b, by simp, hn⟩)
      (fun ρ => by simp [(tval_mkProduct hI hts hp).1, (hT ρ).1]) (fun ρ w hw => ?_)
      (fun ρ => ?_)
    · obtain ⟨x, hx, hw⟩ := Option.bind_eq_some_iff.1 hw
      obtain ⟨y, hy, hw⟩ := Option.bind_eq_some_iff.1 hw
      obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 hw
      simp only [zpowMeaning] at hz; split at hz; · cases hz
      cases hz; rw [denote_val hx, denote_val hy]
    · cases hx : a.denote I ρ <;> cases hy : b.denote I ρ <;> simp [hx, hy, zpowMeaning]
  · unfold mkCall at h
    split at h; · cases h
    split at h
    · rename_i t ht
      simp only [Result.value.injEq] at h; subst h
      split at ht
      · rename_i hp; subst hp
        unfold piecewiseBranch at ht; split at ht
        · rename_i c x y _ _; simp only [Option.some.injEq] at ht; subst ht
          have hc : I.cond (.truth c) [] = some c := hI.1 c
          simp only [Head.piecewise, Term.denote, Term.holds, Term.meanings, hc]
          cases c <;> rfl
        · cases ht
      · cases ht
    · split at h <;> simp only [Result.value.injEq, reduceCtorEq] at h <;> subst h
      · rfl
      · exact congrFun (hK me hd args _ ‹_›) ρ

end Kalyx.Proofs.Terms.Meaning
