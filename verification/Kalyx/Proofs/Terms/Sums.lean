module

public import Kalyx.Statements.Terms
public import Kalyx.Proofs.Terms.Basics
public import Kalyx.Proofs.Terms.Sorting
public import Kalyx.Proofs.Terms.Order

/-!
# Sums

The sum conjuncts of `SumsAndProductsIgnoreOrderAndGrouping` and of
`MergingAddsCoefficientsAndExponents`: `mkSum` does not depend on the order of
its operands (as a result, without canonicity), nor on the grouping of
canonical operands; a sum of values succeeds; and a sum of canonical operands
keeps their constant and the total coefficient of each core, its monomials of
the coefficient 0 being at most the witness monomial. The tools that other
proofs share: the parts of a list and of appended lists (`sumParts_cons`,
`sumParts_append`), the total coefficient of appended monomials
(`coefficientOf_append`), a sum that succeeds (`mkSum_eq_value`), the
cancellation and its witness (`cancelBases`, `cancelMonomials_eq`,
`mem_cancelMonomials`, `filter_zero_cancelMonomials`), and the shape of the
cores of canonical operands and of witnesses, which a sum reads back
(`CoreShape`, `coreShape_sumParts`, `coreShape_witnessCore`,
`sumParts_assembleSum`).
-/

namespace Kalyx.Proofs.Terms.Sums

open Kalyx.Spec.Terms Kalyx.Statements.Terms Kalyx.Proofs.Terms

/-! ## The parts of lists -/

/-- The parts of `t :: ts`: those of `t`, then those of `ts`. -/
public theorem sumParts_cons (t : Term) (ts : List Term) :
    sumParts (t :: ts) =
      ((sumParts [t]).1 + (sumParts ts).1, (sumParts [t]).2 ++ (sumParts ts).2) := by
  cases t <;> simp [sumParts]

/-- The parts of appended lists: the constants added, the monomials appended. -/
public theorem sumParts_append (a b : List Term) :
    sumParts (a ++ b) = ((sumParts a).1 + (sumParts b).1, (sumParts a).2 ++ (sumParts b).2) := by
  induction a with
  | nil => simp [sumParts]
  | cons t a ih => rw [List.cons_append, sumParts_cons, ih, sumParts_cons t a]; simp [add_assoc]

/-- Permuted operands give the same constant and permuted monomials. -/
private theorem sumParts_perm {ts ts' : List Term} (h : ts.Perm ts') :
    (sumParts ts).1 = (sumParts ts').1 ∧ (sumParts ts).2.Perm (sumParts ts').2 := by
  induction h with
  | nil => exact ⟨rfl, .refl _⟩
  | @cons t l₁ l₂ _ ih =>
    rw [sumParts_cons t l₁, sumParts_cons t l₂]; exact ⟨by rw [ih.1], ih.2.append_left _⟩
  | swap x y l =>
    rw [sumParts_cons y (x :: l), sumParts_cons x l, sumParts_cons x (y :: l), sumParts_cons y l]
    exact ⟨add_left_comm _ _ _, List.perm_append_comm_assoc _ _ _⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1.trans ih₂.1, ih₁.2.trans ih₂.2⟩

/-- A sum is a value exactly without conditions, and then the assembled parts. -/
public theorem mkSum_eq_value {o : Orders} {ts : List Term} {u : Term} :
    mkSum o ts = .value u ↔ (∀ t ∈ ts, t.isCondition = false) ∧
      u = assembleSum (sumParts ts).1 (cancelMonomials o (mergeMonomials o (sumParts ts).2)) := by
  unfold mkSum
  split
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    rintro ⟨h', -⟩
    obtain ⟨t, ht, hc⟩ := List.any_eq_true.1 h
    rw [h' t ht] at hc; cases hc
  · rename_i h
    have hv : ∀ t ∈ ts, t.isCondition = false := by simpa using h
    simp only [Result.value.injEq]
    exact ⟨fun e => ⟨hv, e.symm⟩, fun ⟨_, e⟩ => e.symm⟩

/-- `mkSum` does not depend on the order of the operands, canonical or not. -/
public theorem mkSum_perm {o : Orders} (ho : o.Total) {ts ts' : List Term} (h : ts.Perm ts') :
    mkSum o ts = mkSum o ts' := by
  obtain ⟨h1, h2⟩ := sumParts_perm h
  have hany : ts.any Term.isCondition = ts'.any Term.isCondition :=
    Bool.eq_iff_iff.2 (by simp only [List.any_eq_true, h.mem_iff])
  simp only [mkSum, hany, h1, mergeMonomials_perm (termCmp_total o ho) h2]

/-! ## Total coefficients -/

/-- The total coefficient as a sum over all monomials. -/
private theorem coefficientOf_eq (t : Term) (ms : List (ℚ × Term)) :
    coefficientOf t ms = (ms.map fun m => if m.2 = t then m.1 else 0).sum := by
  induction ms with
  | nil => rfl
  | cons m ms ih => by_cases h : m.2 = t <;> simp_all [coefficientOf]

/-- The total coefficient of appended monomials. -/
public theorem coefficientOf_append (t : Term) (a b : List (ℚ × Term)) :
    coefficientOf t (a ++ b) = coefficientOf t a + coefficientOf t b := by
  simp [coefficientOf_eq]

/-- The total coefficient does not depend on the order of the monomials. -/
private theorem coefficientOf_perm (t : Term) {a b : List (ℚ × Term)} (h : a.Perm b) :
    coefficientOf t a = coefficientOf t b := by
  rw [coefficientOf_eq, coefficientOf_eq]; exact (h.map _).sum_eq

/-- Removing the monomials of the coefficient 0 keeps every total coefficient. -/
private theorem coefficientOf_filter (t : Term) (ms : List (ℚ × Term)) :
    coefficientOf t (ms.filter fun m => decide (m.1 ≠ 0)) = coefficientOf t ms := by
  induction ms with
  | nil => rfl
  | cons m ms ih => by_cases h : m.1 = 0 <;> simp_all [coefficientOf_eq]

/-- A core of a total coefficient other than 0 is a core of the monomials. -/
private theorem mem_of_coefficientOf_ne {t : Term} {ms : List (ℚ × Term)}
    (h : coefficientOf t ms ≠ 0) : t ∈ ms.map Prod.snd := by
  by_contra hn
  refine h ?_
  rw [coefficientOf, List.filter_eq_nil_iff.2 fun m hm e =>
    hn (List.mem_map.2 ⟨m, hm, of_decide_eq_true e⟩)]
  rfl

/-! ## Cancellation -/

/-- The bases of the witness monomial that `cancelMonomials` adds to `ms`. -/
@[expose] public def cancelBases (o : Orders) (ms : List (ℚ × Term)) : List Term :=
  maxBases o (uncovered (Term.negBasesPairs (ms.filter fun m => decide (m.1 = 0)))
    (Term.negBasesPairs (ms.filter fun m => decide (m.1 ≠ 0))))

/-- `cancelMonomials`: the nonzero monomials, with the witness inserted when it has bases. -/
public theorem cancelMonomials_eq (o : Orders) (ms : List (ℚ × Term)) :
    cancelMonomials o ms = if cancelBases o ms = [] then ms.filter (fun m => decide (m.1 ≠ 0))
      else insertBy (monomialCmp o) (0, witnessCore (cancelBases o ms))
        (ms.filter fun m => decide (m.1 ≠ 0)) := by
  unfold cancelMonomials cancelBases
  dsimp only
  split <;> simp_all

/-- The monomials of a cancellation: the nonzero ones, and the witness. -/
public theorem mem_cancelMonomials {o : Orders} {ms : List (ℚ × Term)} {m : ℚ × Term} :
    m ∈ cancelMonomials o ms ↔
      (m ∈ ms ∧ m.1 ≠ 0) ∨
        (cancelBases o ms ≠ [] ∧ m = (0, witnessCore (cancelBases o ms))) := by
  rw [cancelMonomials_eq]
  split
  · simp_all
  · rw [(perm_insertBy _ _ _).mem_iff, List.mem_cons, List.mem_filter, decide_eq_true_iff]
    tauto

/-- A cancellation keeps the total coefficient of every core. -/
public theorem coefficientOf_cancelMonomials (o : Orders) (ms : List (ℚ × Term)) (t : Term) :
    coefficientOf t (cancelMonomials o ms) = coefficientOf t ms := by
  rw [cancelMonomials_eq]
  split
  · exact coefficientOf_filter t ms
  · rw [coefficientOf_perm t (perm_insertBy _ _ _), ← coefficientOf_filter t ms]
    simp [coefficientOf_eq]

/-- The monomials of the coefficient 0 of a cancellation: the witness, if any. -/
public theorem filter_zero_cancelMonomials (o : Orders) (ms : List (ℚ × Term)) :
    (cancelMonomials o ms).filter (fun m => decide (m.1 = 0)) =
      if cancelBases o ms = [] then [] else [(0, witnessCore (cancelBases o ms))] := by
  have hnil : (ms.filter fun m => decide (m.1 ≠ 0)).filter (fun m => decide (m.1 = 0)) = [] :=
    List.filter_eq_nil_iff.2 fun m hm => by simp_all
  rw [cancelMonomials_eq]
  split
  · exact hnil
  · exact List.perm_singleton.1 (((perm_insertBy _ _ _).filter _).trans (by simp))

/-- The bases that the cores of total 0 of `X` hold with a negative exponent and
no core of another total holds. -/
private def Unc (X : List (ℚ × Term)) (b : Term) : Prop :=
  (∃ t ∈ X.map Prod.snd, coefficientOf t X = 0 ∧ b ∈ t.negBases) ∧
    ∀ t, coefficientOf t X ≠ 0 → b ∉ t.negBases

/-- The uncovered bases of monomials `L` with the cores of `X`, weighed by `w` as
the total coefficients of `X`, are `Unc X`. -/
private theorem mem_uncovered_iff {L X : List (ℚ × Term)} (w : ℚ × Term → ℚ)
    (hcore : ∀ t, t ∈ L.map Prod.snd ↔ t ∈ X.map Prod.snd)
    (hcoef : ∀ m ∈ L, w m = coefficientOf m.2 X) (b : Term) :
    b ∈ uncovered (Term.negBasesPairs (L.filter fun m => decide (w m = 0)))
        (Term.negBasesPairs (L.filter fun m => decide (w m ≠ 0))) ↔ Unc X b := by
  simp only [mem_uncovered, mem_negBasesPairs, List.mem_filter, decide_eq_true_eq, Unc]
  constructor
  · rintro ⟨⟨m, ⟨hm, h0⟩, hb⟩, hn⟩
    refine ⟨⟨m.2, (hcore _).1 (List.mem_map_of_mem hm), (hcoef m hm).symm.trans h0, hb⟩,
      fun t ht hbt => hn ?_⟩
    obtain ⟨m', hm', rfl⟩ := List.mem_map.1 ((hcore t).2 (mem_of_coefficientOf_ne ht))
    exact ⟨m', ⟨hm', by rwa [hcoef m' hm']⟩, hbt⟩
  · rintro ⟨⟨t, ht, h0, hb⟩, hn⟩
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ((hcore t).2 ht)
    exact ⟨⟨m, ⟨hm, by rwa [hcoef m hm]⟩, hb⟩,
      fun ⟨m', ⟨hm', h'⟩, hb'⟩ => hn m'.2 (by rwa [← hcoef m' hm']) hb'⟩

/-- The uncovered bases of merged monomials are `Unc` of the monomials. -/
private theorem cancelBases_merge {o : Orders} (hc : TotalCmp (Term.cmp o)) (X : List (ℚ × Term))
    (b : Term) :
    b ∈ uncovered (Term.negBasesPairs ((mergeMonomials o X).filter fun m => decide (m.1 = 0)))
      (Term.negBasesPairs ((mergeMonomials o X).filter fun m => decide (m.1 ≠ 0))) ↔ Unc X b :=
  mem_uncovered_iff Prod.fst (mem_cores_mergeMonomials hc X)
    (fun _ hm => ((mem_mergeMonomials hc).1 hm).2) b

/-- The bases of a witness are not constants. -/
private theorem cancelBases_nonconst {o : Orders} {ms : List (ℚ × Term)} {c : Term}
    (h : c ∈ cancelBases o ms) : c.isConstant = false := by
  obtain ⟨m, -, hm⟩ := mem_negBasesPairs.1 (mem_uncovered.1 (maxBases_subset h)).1
  exact negBases_isConstant hm

/-- `N` of the core of a witness: its bases and their `N`. -/
private theorem mem_negBases_witnessCore {bs : List Term} (h : ∀ b ∈ bs, b.isConstant = false)
    {x : Term} : x ∈ (witnessCore bs).negBases ↔ ∃ b ∈ bs, x = b ∨ x ∈ b.negBases := by
  rw [← mem_negBases_reciprocals h]
  rcases bs with _ | ⟨b, _ | ⟨c, bs⟩⟩ <;>
    simp [witnessCore, Term.negBases, Term.negBasesList]

/-- The merged monomials of the coefficients other than 0 depend only on the totals. -/
private theorem rest_merge_congr {o : Orders} (hc : TotalCmp (Term.cmp o))
    {X Y : List (ℚ × Term)} (hκ : ∀ t, coefficientOf t X = coefficientOf t Y) :
    (mergeMonomials o X).filter (fun m => decide (m.1 ≠ 0)) =
      (mergeMonomials o Y).filter (fun m => decide (m.1 ≠ 0)) := by
  have := hc.1
  have key : ∀ (Z : List (ℚ × Term)) m,
      m ∈ (mergeMonomials o Z).filter (fun m => decide (m.1 ≠ 0)) ↔
        m.1 = coefficientOf m.2 Z ∧ m.1 ≠ 0 := fun Z m => by
    rw [List.mem_filter, mem_mergeMonomials hc, decide_eq_true_iff]
    exact ⟨fun ⟨⟨_, h⟩, h'⟩ => ⟨h, h'⟩,
      fun ⟨h, h'⟩ => ⟨⟨mem_of_coefficientOf_ne fun e => h' (h.trans e), h⟩, h'⟩⟩
  exact eq_of_strictlyIncreasing_map Prod.snd
    (strictlyIncreasing_filter_map (mergeMonomials_strictlyIncreasing hc X) _)
    (strictlyIncreasing_filter_map (mergeMonomials_strictlyIncreasing hc Y) _)
    fun m => by rw [key, key, hκ]

/-- The cancellation of merged monomials depends only on the totals and on `Unc`. -/
private theorem cancel_merge_congr {o : Orders} (hc : TotalCmp (Term.cmp o))
    {X Y : List (ℚ × Term)} (hκ : ∀ t, coefficientOf t X = coefficientOf t Y)
    (hU : ∀ b, Unc X b ↔ Unc Y b) :
    cancelMonomials o (mergeMonomials o X) = cancelMonomials o (mergeMonomials o Y) := by
  have h2 : cancelBases o (mergeMonomials o X) = cancelBases o (mergeMonomials o Y) :=
    maxBases_congr hc fun b =>
      (cancelBases_merge hc X b).trans ((hU b).trans (cancelBases_merge hc Y b).symm)
  rw [cancelMonomials_eq, cancelMonomials_eq, rest_merge_congr hc hκ, h2]

/-- A cancelled merge keeps `N` of the cores of the monomials. -/
public theorem negBases_cancel_merge {o : Orders} (hc : TotalCmp (Term.cmp o))
    {ms : List (ℚ × Term)} {b : Term} (h : b ∈ Term.negBasesPairs ms) :
    b ∈ Term.negBasesPairs (cancelMonomials o (mergeMonomials o ms)) := by
  obtain ⟨⟨a, t⟩, hm, hb⟩ := mem_negBasesPairs.1 h
  rw [mem_negBasesPairs]
  by_cases hB : ∃ t', coefficientOf t' ms ≠ 0 ∧ b ∈ t'.negBases
  · obtain ⟨t', h', hb'⟩ := hB
    exact ⟨(coefficientOf t' ms, t'), mem_cancelMonomials.2
      (.inl ⟨(mem_mergeMonomials hc).2 ⟨mem_of_coefficientOf_ne h', rfl⟩, h'⟩), hb'⟩
  · have hU : Unc ms b := ⟨⟨t, List.mem_map_of_mem (f := Prod.snd) hm,
      by_contra fun h => hB ⟨t, h, hb⟩, hb⟩, fun t' h hb' => hB ⟨t', h, hb'⟩⟩
    obtain ⟨c, hc', hbc⟩ :
        ∃ c ∈ cancelBases o (mergeMonomials o ms), b = c ∨ b ∈ c.negBases := by
      rcases maxBases_cover o _ ((cancelBases_merge hc ms b).2 hU) with h | ⟨m, hm, h⟩
      exacts [⟨b, h, .inl rfl⟩, ⟨m, hm, .inr h⟩]
    exact ⟨_, mem_cancelMonomials.2 (.inr ⟨List.ne_nil_of_mem hc', rfl⟩),
      (mem_negBases_witnessCore fun _ hc => cancelBases_nonconst hc).2 ⟨c, hc', hbc⟩⟩

/-- Replacing monomials `B` among others by their cancelled merge does not change the
cancelled merge. -/
public theorem cancelMonomials_group {o : Orders} (hc : TotalCmp (Term.cmp o))
    (A B D : List (ℚ × Term)) :
    cancelMonomials o (mergeMonomials o (A ++ cancelMonomials o (mergeMonomials o B) ++ D)) =
      cancelMonomials o (mergeMonomials o (A ++ B ++ D)) := by
  have hκ : ∀ t, coefficientOf t (A ++ cancelMonomials o (mergeMonomials o B) ++ D) =
      coefficientOf t (A ++ B ++ D) := fun t => by
    simp only [coefficientOf_append, coefficientOf_cancelMonomials, coefficientOf_mergeMonomials hc]
  refine cancel_merge_congr hc hκ fun b => ?_
  simp only [Unc, hκ, List.map_append, List.mem_append]
  constructor
  · rintro ⟨⟨t, ht, h0, hb⟩, hn⟩
    refine ⟨?_, hn⟩
    rcases ht with (ht | ht) | ht
    · exact ⟨t, .inl (.inl ht), h0, hb⟩
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ht
      rcases mem_cancelMonomials.1 hm with ⟨hm, -⟩ | ⟨-, rfl⟩
      · exact ⟨m.2, .inl (.inr ((mem_cores_mergeMonomials hc B _).1 (List.mem_map_of_mem hm))),
          h0, hb⟩
      · -- A base of the witness lies in or below a base of a core of `B` of total 0.
        obtain ⟨c, hc', hbc⟩ :=
          (mem_negBases_witnessCore fun _ hc => cancelBases_nonconst hc).1 hb
        obtain ⟨⟨t', ht', -, hct'⟩, -⟩ := (cancelBases_merge hc B c).1 (maxBases_subset hc')
        have hbt' : b ∈ t'.negBases := hbc.elim (fun e => e ▸ hct') (negBases_trans hct')
        exact ⟨t', .inl (.inr ht'), by_contra fun h => hn t' h hbt', hbt'⟩
    · exact ⟨t, .inr ht, h0, hb⟩
  · rintro ⟨⟨t, ht, h0, hb⟩, hn⟩
    refine ⟨?_, hn⟩
    rcases ht with (ht | ht) | ht
    · exact ⟨t, .inl (.inl ht), h0, hb⟩
    · obtain ⟨m', hm', rfl⟩ := List.mem_map.1 ht
      obtain ⟨m, hm, hbm⟩ :=
        mem_negBasesPairs.1 (negBases_cancel_merge hc (mem_negBasesPairs.2 ⟨m', hm', hb⟩))
      exact ⟨m.2, .inl (.inr (List.mem_map_of_mem hm)), by_contra fun h => hn _ h hbm, hbm⟩
    · exact ⟨t, .inr ht, h0, hb⟩

/-! ## Reading a sum back -/

/-- A core that `sumParts` reads back as itself: a core whose factors give it back. -/
@[expose] public def CoreShape (t : Term) : Prop :=
  t.coreOk = true ∧ productCore t.coreFactors = t

/-- The sum assembled from monomials whose cores read back is read back as its
constant and its monomials. -/
public theorem sumParts_assembleSum (c : ℚ) {ms : List (ℚ × Term)}
    (h : ∀ m ∈ ms, CoreShape m.2) : sumParts [assembleSum c ms] = (c, ms) := by
  rcases ms with _ | ⟨⟨a, t⟩, _ | ⟨n, ms⟩⟩
  · simp [assembleSum, sumParts]
  · obtain ⟨hok, hpc⟩ := h (a, t) (List.mem_singleton_self _)
    simp only [assembleSum]
    split_ifs with hc ha
    · subst hc ha
      cases t <;> simp_all [sumParts, Term.coreOk, Term.coreFactors, productCore]
    · simp [sumParts, hc, hpc]
    · simp [sumParts]
  · simp [assembleSum, sumParts]

/-- The core of the witness monomial reads back. -/
public theorem coreShape_witnessCore (bs : List Term) : CoreShape (witnessCore bs) := by
  rcases bs with _ | ⟨b, _ | ⟨c, bs⟩⟩ <;>
    exact ⟨by simp [witnessCore, Term.coreOk, Term.reciprocal], rfl⟩

/-- A core that is a canonical node reads back. -/
private theorem coreShape_of_nodeOk {o : Orders} {me : ℕ} {R : RegistryRules} {t : Term}
    (hc : t.coreOk = true) (hn : t.nodeOk o me R = true) : CoreShape t := by
  refine ⟨hc, ?_⟩
  cases t with
  | product a fs =>
    simp only [Term.coreOk, beq_iff_eq] at hc; subst hc
    rcases fs with _ | ⟨f, _ | ⟨g, fs⟩⟩
    · rfl
    · simp [Term.nodeOk, canonicalProduct] at hn
    · rfl
  | _ => rfl

/-- The core of the monomial of a canonical product reads back. -/
private theorem coreShape_productCore {o : Orders} {c : ℚ} {fs : List Term}
    (h : canonicalProduct o c fs = true) : CoreShape (productCore fs) := by
  rcases fs with _ | ⟨f, _ | ⟨g, fs⟩⟩
  · simp [canonicalProduct] at h
  · cases f <;> simp_all [canonicalProduct, Term.factorOk, CoreShape, Term.coreOk, productCore,
      Term.coreFactors]
  · exact ⟨by simp [productCore, Term.coreOk], rfl⟩

/-- The cores of the monomials of a canonical value read back. -/
private theorem coreShape_one {o : Orders} {me : ℕ} {R : RegistryRules} {t : Term}
    (hn : ∀ x ∈ t.nodes, x.nodeOk o me R = true) (hv : t.isCondition = false) :
    ∀ m ∈ (sumParts [t]).2, CoreShape m.2 := by
  have hroot := hn t (mem_nodes_self t)
  cases t with
  | sum c ms =>
    simp only [sumParts, List.append_nil]
    intro m hm
    simp only [Term.nodeOk, canonicalSum, Bool.and_eq_true, List.all_eq_true] at hroot
    exact coreShape_of_nodeOk (hroot.1.1.2 m hm) (hn m.2 (by
      rw [Term.nodes]; exact .tail _ (mem_nodesPairs.2 ⟨m, hm, mem_nodes_self _⟩)))
  | product c fs =>
    simp only [sumParts, List.mem_singleton]
    rintro m rfl
    exact coreShape_productCore hroot
  | condition => simp [Term.isCondition] at hv
  | number => simp [sumParts]
  | _ => simp only [sumParts, List.mem_singleton]; rintro m rfl; exact ⟨rfl, rfl⟩

/-- The cores of the monomials of canonical values read back. -/
public theorem coreShape_sumParts {o : Orders} {me : ℕ} {R : RegistryRules} {ts : List Term}
    (h : ∀ t ∈ ts, Term.Canonical o me R t) (hv : ∀ t ∈ ts, t.isCondition = false) :
    ∀ m ∈ (sumParts ts).2, CoreShape m.2 := by
  induction ts with
  | nil => simp [sumParts]
  | cons t ts ih =>
    rw [sumParts_cons]
    intro m hm
    rcases List.mem_append.1 hm with hm | hm
    · exact coreShape_one (List.all_eq_true.1 (h t (by simp)).1) (hv t (by simp)) m hm
    · exact ih (fun t ht => h t (by simp [ht])) (fun t ht => hv t (by simp [ht])) m hm

/-- The sum of canonical operands is read back as their constant and their
cancelled merged monomials. -/
public theorem mkSum_reread {o : Orders} {me : ℕ} {R : RegistryRules} (ho : o.Total)
    {ts : List Term} {u : Term} (h : ∀ t ∈ ts, Term.Canonical o me R t)
    (hu : mkSum o ts = .value u) :
    sumParts [u] = ((sumParts ts).1, cancelMonomials o (mergeMonomials o (sumParts ts).2)) := by
  obtain ⟨hv, rfl⟩ := mkSum_eq_value.1 hu
  refine sumParts_assembleSum _ fun m hm => ?_
  rcases mem_cancelMonomials.1 hm with ⟨hm, -⟩ | ⟨-, rfl⟩
  · obtain ⟨m', hm', e⟩ := List.mem_map.1
      ((mem_cores_mergeMonomials (termCmp_total o ho) _ m.2).1 (List.mem_map_of_mem hm))
    exact e ▸ coreShape_sumParts h hv m' hm'
  · exact coreShape_witnessCore _

/-! ## The conjuncts -/

/-- `SumsAndProductsIgnoreOrderAndGrouping`, sums of permuted operands. -/
public theorem sumsIgnoreOrder (o : Orders) (maxExponent : ℕ) (R : RegistryRules) (ho : o.Total) :
    ∀ ts ts' u u', (∀ t ∈ ts, Term.Canonical o maxExponent R t) → ts.Perm ts' →
      mkSum o ts = .value u → mkSum o ts' = .value u' → u = u' := fun _ _ _ _ _ hp hu hu' => by
  rw [mkSum_perm ho hp, hu'] at hu; exact (Result.value.inj hu).symm

/-- `SumsAndProductsIgnoreOrderAndGrouping`, sums of grouped operands. -/
public theorem sumsIgnoreGrouping (o : Orders) (maxExponent : ℕ) (R : RegistryRules)
    (ho : o.Total) :
    ∀ ts₁ ts₂ ts₃ s u u',
      (∀ t ∈ ts₁ ++ ts₂ ++ ts₃, Term.Canonical o maxExponent R t) →
      mkSum o ts₂ = .value s → mkSum o (ts₁ ++ ts₂ ++ ts₃) = .value u →
      mkSum o (ts₁ ++ s :: ts₃) = .value u' → u = u' := by
  intro ts₁ ts₂ ts₃ s u u' hc hs hu hu'
  have hr := mkSum_reread ho (fun t ht => hc t (by simp [ht])) hs
  obtain ⟨-, rfl⟩ := mkSum_eq_value.1 hu
  obtain ⟨-, rfl⟩ := mkSum_eq_value.1 hu'
  rw [show ts₁ ++ s :: ts₃ = ts₁ ++ [s] ++ ts₃ by simp]
  simp only [sumParts_append, hr]
  rw [cancelMonomials_group (termCmp_total o ho)]

/-- `SumsAndProductsIgnoreOrderAndGrouping`, a sum of values succeeds. -/
public theorem sumsOfValuesSucceed (o : Orders) :
    ∀ ts : List Term, (∀ t ∈ ts, t.isCondition = false) → ∃ u, mkSum o ts = .value u :=
  fun _ h => ⟨_, mkSum_eq_value.2 ⟨h, rfl⟩⟩

/-- `MergingAddsCoefficientsAndExponents`, the parts of a sum. -/
public theorem sumsMergeCoefficients (o : Orders) (maxExponent : ℕ) (R : RegistryRules)
    (ho : o.Total) :
    ∀ ts u, (∀ t ∈ ts, Term.Canonical o maxExponent R t) → mkSum o ts = .value u →
      let ms := (sumParts ts).2
      let cancelled := ms.filter fun m => coefficientOf m.2 ms = 0
      let kept := ms.filter fun m => coefficientOf m.2 ms ≠ 0
      let bs := maxBases o (uncovered (Term.negBasesPairs cancelled) (Term.negBasesPairs kept))
      (sumParts [u]).1 = (sumParts ts).1 ∧
        (∀ t, coefficientOf t (sumParts [u]).2 = coefficientOf t ms) ∧
        (sumParts [u]).2.filter (fun m => m.1 = 0) =
          if bs = [] then [] else [(0, witnessCore bs)] := by
  intro ts u hc hu
  have hT := termCmp_total o ho
  dsimp only
  rw [mkSum_reread ho hc hu]
  dsimp only
  rw [filter_zero_cancelMonomials]
  refine ⟨rfl, fun t => by
    rw [coefficientOf_cancelMonomials, coefficientOf_mergeMonomials hT], ?_⟩
  generalize (sumParts ts).2 = ms
  have e : cancelBases o (mergeMonomials o ms) =
      maxBases o (uncovered (Term.negBasesPairs (ms.filter fun m => coefficientOf m.2 ms = 0))
        (Term.negBasesPairs (ms.filter fun m => coefficientOf m.2 ms ≠ 0))) :=
    maxBases_congr hT fun b => (cancelBases_merge hT _ b).trans
      (mem_uncovered_iff (fun m => coefficientOf m.2 ms) (fun _ => Iff.rfl) (fun _ _ => rfl) b).symm
  rw [e]

end Kalyx.Proofs.Terms.Sums
