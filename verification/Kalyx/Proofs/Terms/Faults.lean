module

public import Kalyx.Statements.Terms

/-!
# The faults of strict evaluation

A helper module, not registered, for the proof of
`StrictEvaluationFaults`. An exponent beyond the bound fails with `ResourceLimit` naming
`max_exponent` where it is checked: the argument of a power, the sum of two
exponents of one key in a product and the product of two exponents in a
power of a power. `DivisionByZero` arises only from the strict power of a
rational in `mkPower`: of a number base, of the coefficient of a product and
of the content of a sum, so exactly for a negative power of a zero base
(`ZeroBase`): the number 0, a product with the coefficient 0 or a sum of the
content 0, each of which is 0 wherever it is defined; sums and products never
divide by zero. A canonical sum has a content other than 0.
-/

namespace Kalyx.Proofs.Terms

open Kalyx.Spec.Terms Kalyx.Spec.Fields Kalyx.Statements.Terms

/-! ## Results that are not `DivisionByZero` -/

/-- A result that is not the fault `DivisionByZero`. -/
private abbrev NoDiv {α : Type} (r : Result α) : Prop := r ≠ .fault .divisionByZero

/-- A bound value is the function at the value. -/
private theorem value_bind {α β : Type} (v : α) (f : α → Result β) :
    (Result.value v >>= f) = f v := rfl

/-- A pure value is the value. -/
private theorem pure_eq {α : Type} (v : α) : (pure v : Result α) = .value v := rfl

/-- A bound limit is the limit. -/
private theorem limit_bind {α β : Type} (l : LimitField) (f : α → Result β) :
    (Result.resourceLimit l >>= f) = .resourceLimit l := rfl

/-- Closes `NoDiv` of a value, a limit or another fault. -/
local macro "nodiv" : tactic => `(tactic| (intro h; cases h))

/-- A bind is not `DivisionByZero` when neither its argument nor its function
is. -/
private theorem bind_noDiv {α β : Type} {x : Result α} {f : α → Result β}
    (hx : NoDiv x) (hf : ∀ v, NoDiv (f v)) : NoDiv (x >>= f) := by
  cases x with
  | value v => exact hf v
  | fault e => intro h; exact hx (by cases h; rfl)
  | resourceLimit l => nodiv

/-- A bind whose function never gives `DivisionByZero` gives it exactly when
its argument does. -/
private theorem bind_div_of {α β : Type} {x : Result α} {f : α → Result β}
    (hf : ∀ v, NoDiv (f v)) : x >>= f = .fault .divisionByZero ↔ x = .fault .divisionByZero := by
  cases x with
  | value v => exact ⟨fun h => absurd h (hf v), nofun⟩
  | fault e => exact ⟨fun h => by cases h; rfl, fun h => by cases h; rfl⟩
  | resourceLimit l => exact ⟨nofun, nofun⟩

/-- The loop of `mapM` is not `DivisionByZero` when `f` gives no
`DivisionByZero` on any element of the list. -/
private theorem loop_noDiv {α β : Type} (f : α → Result β) :
    ∀ (l : List α) (bs : List β), (∀ a ∈ l, NoDiv (f a)) → NoDiv (List.mapM.loop f l bs)
  | [], _, _ => by rw [List.mapM.loop]; nodiv
  | a :: l, bs, h => by
    rw [List.mapM.loop]
    exact bind_noDiv (h a (by simp)) fun v => loop_noDiv f l _ fun x hx => h x (by simp [hx])

/-- `mapM` is not `DivisionByZero` when `f` gives no `DivisionByZero` on any
element of the list. -/
private theorem mapM_noDiv {α β : Type} (f : α → Result β) (l : List α)
    (h : ∀ a ∈ l, NoDiv (f a)) : NoDiv (l.mapM f) :=
  loop_noDiv f l [] h

/-! ## Products and sums never divide by zero -/

/-- `itemParts` never divides by zero. -/
private theorem itemParts_noDiv (me : ℕ) (q : ℤ) (t : Term) : NoDiv (itemParts me q t) := by
  unfold itemParts checkExponent
  repeat' split
  all_goals nodiv

/-- `factorParts` never divides by zero. -/
private theorem factorParts_noDiv (me : ℕ) (q : ℤ) (t : Term) : NoDiv (factorParts me q t) := by
  unfold factorParts
  split
  · nodiv
  · exact bind_noDiv (mapM_noDiv _ _ fun x _ => itemParts_noDiv me q x) fun _ => by nodiv
  · exact itemParts_noDiv me q _

/-- `reduceItem` never divides by zero. -/
private theorem reduceItem_noDiv (me : ℕ) (x : Term × ℤ) : NoDiv (reduceItem me x) := by
  obtain ⟨b, k⟩ := x
  unfold reduceItem checkExponent
  repeat' split
  all_goals first
    | nodiv
    | exact bind_noDiv (factorParts_noDiv _ _ _) fun _ => by nodiv

/-- `settleItems` never divides by zero. -/
private theorem settleItems_noDiv (o : Orders) (me : ℕ) :
    ∀ (fuel : ℕ) (p : ProductParts), NoDiv (settleItems o me fuel p)
  | 0, _ => by rw [settleItems]; nodiv
  | fuel + 1, p => by
    rw [settleItems]
    refine bind_noDiv (mapM_noDiv _ _ fun x _ => reduceItem_noDiv me x) fun rs => ?_
    dsimp only
    split
    · nodiv
    · exact settleItems_noDiv o me fuel _

/-- `buildProduct` never divides by zero. -/
private theorem buildProduct_noDiv (o : Orders) (me : ℕ) (p : ProductParts) :
    NoDiv (buildProduct o me p) := by
  unfold buildProduct
  refine bind_noDiv (settleItems_noDiv o me _ _) fun _ => ?_
  dsimp only
  split <;> nodiv

/-- A product never fails with `DivisionByZero`. -/
public theorem mkProduct_ne_divisionByZero (o : Orders) (me : ℕ) (ts : List Term) :
    mkProduct o me ts ≠ .fault .divisionByZero := by
  unfold mkProduct
  split
  · nodiv
  · refine bind_noDiv ?_ fun p => buildProduct_noDiv o me p
    exact bind_noDiv (mapM_noDiv _ _ fun x _ => factorParts_noDiv me 1 x) fun _ => by nodiv

/-- A sum never fails with `DivisionByZero`. -/
public theorem mkSum_ne_divisionByZero (o : Orders) (ts : List Term) :
    mkSum o ts ≠ .fault .divisionByZero := by
  unfold mkSum
  split <;> nodiv

/-- The merges of powers never divide by zero. -/
private theorem mergePowers_noDiv (me : ℕ) (b : Term) (k : ℤ) : NoDiv (mergePowers me b k) := by
  match b with
  | .power c j =>
    rw [mergePowers]
    unfold checkExponent
    split
    · split
      · nodiv
      · exact mergePowers_noDiv me c (j * k)
    · nodiv
  | .number _ | .constant _ | .symbol _ | .call .. | .product .. | .sum .. | .condition .. =>
    simp [NoDiv, mergePowers]

/-- `mergedPower` never divides by zero. -/
private theorem mergedPower_noDiv (o : Orders) (me : ℕ) (b : Term) (k : ℤ) :
    NoDiv (mergedPower o me b k) := by
  unfold mergedPower
  refine bind_noDiv (mergePowers_noDiv me b k) fun x => ?_
  obtain ⟨c, j⟩ := x
  dsimp only
  split
  · nodiv
  · split
    · nodiv
    · exact buildProduct_noDiv o me _

/-! ## Where a power divides by zero -/

/-- The bases whose negative powers divide by zero: the number 0, a product
with the coefficient 0 and a sum of the content 0. -/
private def ZeroBase : Term → Prop
  | .number r => r = 0
  | .product c _ => c = 0
  | .sum c ms => sumContent c ms = 0
  | _ => False

/-- A map of a result is `DivisionByZero` exactly when the result is. -/
private theorem map_div {α β : Type} (f : α → β) (x : Result α) :
    x.map f = .fault .divisionByZero ↔ x = .fault .divisionByZero := by
  cases x <;> simp [Result.map]

/-- The strict power of a rational divides by zero exactly for a negative
power of 0. -/
private theorem ratPowOp_div (r : ℚ) (k : ℤ) :
    Result.ofOutcome (ratPowOp r k) = .fault .divisionByZero ↔ r = 0 ∧ k < 0 := by
  unfold ratPowOp ratPow
  split
  · exact ⟨fun _ => by assumption, fun _ => rfl⟩
  · exact ⟨nofun, fun h => absurd h (by assumption)⟩

/-- The power of a base that is not a number, past the check and the exponents
0 and 1, divides by zero exactly for a negative power of a zero base. -/
private theorem distributedPower_div_iff (o : Orders) (me : ℕ) (b : Term) (k : ℤ)
    (hb : ∀ r, b ≠ .number r) :
    distributedPower o me b k = .fault .divisionByZero ↔ k < 0 ∧ ZeroBase b := by
  cases b with
  | number r => exact absurd rfl (hb r)
  | product c fs =>
    rw [distributedPower, bind_div_of, ratPowOp_div]
    · exact and_comm
    · exact fun _ => bind_noDiv (mapM_noDiv _ _ fun f _ => mergedPower_noDiv o me f k)
        fun _ => mkProduct_ne_divisionByZero o me _
  | sum c ms =>
    rw [distributedPower, bind_div_of, ratPowOp_div]
    · exact and_comm
    · exact fun _ => buildProduct_noDiv o me _
  | _ =>
    simp only [distributedPower, ZeroBase, and_false, iff_false]
    exact mergedPower_noDiv o me _ k

/-- A power divides by zero exactly when its exponent is within the bound and
negative and its base is a zero base. -/
private theorem mkPower_div_iff (o : Orders) (me : ℕ) (b : Term) (k : ℤ) :
    mkPower o me b k = .fault .divisionByZero ↔
      k.natAbs ≤ exponentBound me ∧ k < 0 ∧ ZeroBase b := by
  unfold mkPower checkExponent
  by_cases hk : exponentBound me < k.natAbs
  · constructor
    · intro h
      simp [hk] at h
    · intro h
      exact absurd h.1 (by omega)
  have hle : k.natAbs ≤ exponentBound me := by omega
  simp only [hk, ↓reduceIte, hle, true_and]
  cases b with
  | number r =>
    simp only [Term.isCondition, Bool.false_eq_true, ↓reduceIte, map_div, ratPowOp_div]
    exact and_comm
  | condition s ops => simp [Term.isCondition, ZeroBase]
  | _ =>
    simp only [Term.isCondition, Bool.false_eq_true, ↓reduceIte]
    split
    · exact ⟨nofun, fun h => absurd h.1 (by omega)⟩
    · split
      · exact ⟨nofun, fun h => absurd h.1 (by omega)⟩
      · exact distributedPower_div_iff o me _ k fun _ => nofun

/-- A quotient divides by zero exactly when the power `-1` of its divisor
does. -/
private theorem mkDivide_div_iff (o : Orders) (me : ℕ) (a b : Term) :
    mkDivide o me a b = .fault .divisionByZero ↔ mkPower o me b (-1) = .fault .divisionByZero := by
  unfold mkDivide
  exact bind_div_of fun _ => mkProduct_ne_divisionByZero o me _

/-! ## Zero bases -/

/-- A content of 0 means the constant 0 and only coefficients 0. -/
private theorem sumContent_eq_zero {c : ℚ} :
    ∀ (ms : List (ℚ × Term)), sumContent c ms = 0 → c = 0 ∧ ∀ m ∈ ms, m.1 = 0
  | [], h => ⟨by simpa [sumContent] using h, by simp⟩
  | (a, t) :: ms, h => by
    rw [sumContent] at h
    split at h
    · obtain ⟨h1, h2⟩ := sumContent_eq_zero ms h
      exact ⟨h1, List.forall_mem_cons.2 ⟨by assumption, h2⟩⟩
    · exact absurd h (by assumption)

/-- A canonical sum has a content other than 0: it has at least two parts and
at most one monomial with the coefficient 0. -/
private theorem content_ne_zero {o : Orders} {me : ℕ} {R : RegistryRules} {c : ℚ}
    {ms : List (ℚ × Term)} (h : Term.Canonical o me R (.sum c ms)) : sumContent c ms ≠ 0 := by
  intro h0
  obtain ⟨hc, hms⟩ := sumContent_eq_zero ms h0
  have hs : canonicalSum o c ms = true := by
    have := h.1
    simp only [Term.shapeOk, Term.nodes, List.all_cons, Bool.and_eq_true] at this
    exact this.1
  have hf : ms.filter (fun m => decide (m.1 = 0)) = ms :=
    List.filter_eq_self.2 fun m hm => by simp [hms m hm]
  unfold canonicalSum at hs
  rw [hf, hc] at hs
  match ms, hs with
  | [], hs => simp at hs
  | [_], hs => simp at hs
  | _ :: _ :: _, hs => simp at hs

/-- On a canonical term, the zero bases are the number 0 and the products with
the coefficient 0. -/
private theorem zeroBase_iff {o : Orders} {me : ℕ} {R : RegistryRules} {b : Term}
    (h : Term.Canonical o me R b) : ZeroBase b ↔ b = .number 0 ∨ ∃ fs, b = .product 0 fs := by
  cases b with
  | number r => simp [ZeroBase]
  | product c fs => simp [ZeroBase]
  | sum c ms => simp [ZeroBase, content_ne_zero h]
  | _ => simp [ZeroBase]

/-- Monomials with the coefficient 0 add up to 0 where they are defined. -/
private theorem denotePairs_zero (I : Interp) (ρ : Assignment) :
    ∀ (ms : List (ℚ × Term)), (∀ m ∈ ms, m.1 = 0) →
      Term.denotePairs I ρ ms = none ∨ Term.denotePairs I ρ ms = some 0
  | [], _ => by simp [Term.denotePairs]
  | (a, t) :: ms, h => by
    have ha : a = 0 := h (a, t) (by simp)
    rcases denotePairs_zero I ρ ms (fun m hm => h m (by simp [hm])) with h' | h' <;>
      cases hv : Term.denote I ρ t <;> simp [Term.denotePairs, h', hv, ha]

/-- A zero base is undefined or 0. -/
private theorem denote_zero (I : Interp) (ρ : Assignment) (b : Term) (hb : ZeroBase b) :
    b.denote I ρ = none ∨ b.denote I ρ = some 0 := by
  cases b with
  | number r =>
    simp only [ZeroBase] at hb
    simp [Term.denote, hb]
  | product c fs =>
    simp only [ZeroBase] at hb
    cases h : Term.denoteList I ρ fs <;> simp [Term.denote, h, hb]
  | sum c ms =>
    obtain ⟨hc, hms⟩ := sumContent_eq_zero ms hb
    rcases denotePairs_zero I ρ ms hms with h | h <;> simp [Term.denote, h, hc]
  | _ => simp [ZeroBase] at hb

/-- A negative power of a zero base is undefined. -/
private theorem zpow_zeroBase (I : Interp) (ρ : Assignment) (b : Term) (k : ℤ)
    (hb : ZeroBase b) (hk : k < 0) : (b.denote I ρ).bind (fun v => zpowMeaning v k) = none := by
  rcases denote_zero I ρ b hb with h | h <;> simp [h, zpowMeaning, hk]

/-! ## Exponents beyond the bound -/

/-- `[x^j, x^k]` with one sign: the merged exponent `j + k` is checked. -/
private theorem product_two_powers (o : Orders) (me : ℕ) (b : Term) (j k : ℤ)
    (hjk : 0 < j * k) (hb : exponentBound me < (j + k).natAbs) :
    mkProduct o me [.power b j, .power b k] = .resourceLimit .exponent := by
  have hj : j ≠ 0 := by rintro rfl; simp at hjk
  have hk : k ≠ 0 := by rintro rfl; simp at hjk
  have hsign : decide (j < 0) = decide (k < 0) := by
    rw [decide_eq_decide]
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hjk with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      exact ⟨fun _ => by omega, fun _ => by omega⟩
  have hkey : Key.of b j = Key.of b k := by simp only [Key.of, hsign]
  have hred : ∀ s : ℤ, exponentBound me < s.natAbs →
      [(b, s)].mapM (reduceItem me) = .resourceLimit .exponent := by
    intro s hs
    simp [List.mapM, List.mapM.loop, reduceItem, checkExponent, hs, limit_bind]
  have hm : mergeItems o [(b, j), (b, k)] = [(b, j + k)] ∨
      mergeItems o [(b, j), (b, k)] = [(b, k + j)] := by
    unfold mergeItems
    simp only [sortBy, insertBy]
    split <;> simp [mergeAdjacent, hkey]
  have hbuild : buildProduct o me ⟨1, [(b, j), (b, k)], []⟩ = .resourceLimit .exponent := by
    unfold buildProduct
    rw [settleItems]
    dsimp only
    rcases hm with hm | hm <;> rw [hm]
    · rw [hred _ hb]; rfl
    · rw [hred _ (by rw [add_comm]; exact hb)]; rfl
  unfold mkProduct
  simp only [List.any_cons, List.any_nil, Term.isCondition, Bool.or_false, Bool.false_eq_true,
    ↓reduceIte]
  by_cases h1 : exponentBound me < j.natAbs
  · have : productParts me [.power b j, .power b k] = .resourceLimit .exponent := by
      simp [productParts, List.mapM, List.mapM.loop, factorParts, itemParts, checkExponent, hj,
        h1, limit_bind]
    rw [this]; rfl
  by_cases h2 : exponentBound me < k.natAbs
  · have : productParts me [.power b j, .power b k] = .resourceLimit .exponent := by
      simp [productParts, List.mapM, List.mapM.loop, factorParts, itemParts, checkExponent, hj,
        hk, h1, h2, value_bind, limit_bind]
    rw [this]; rfl
  have hp : productParts me [.power b j, .power b k] = .value ⟨1, [(b, j), (b, k)], []⟩ := by
    simp [productParts, List.mapM, List.mapM.loop, factorParts, itemParts, checkExponent, hj, hk,
      h1, h2, pure_eq, value_bind, ProductParts.append, ProductParts.unit]
  rw [hp, value_bind]
  exact hbuild

/-! ## The statement -/

/-- The faults of strict evaluation. -/
public theorem strictEvaluationFaults_holds : StrictEvaluationFaults := by
  intro o me R _
  dsimp only
  have div8 : ∀ (I : Interp) b k, mkPower o me b k = .fault .divisionByZero →
      ∀ ρ, (b.denote I ρ).bind (fun v => zpowMeaning v k) = none := by
    intro I b k h ρ
    obtain ⟨_, hk, hz⟩ := (mkPower_div_iff o me b k).1 h
    exact zpow_zeroBase I ρ b k hz hk
  refine ⟨?_, ?_, ?_, ?_, ?_, fun ts => mkSum_ne_divisionByZero o ts,
    fun ts => mkProduct_ne_divisionByZero o me ts, div8, ?_, ?_, ?_⟩
  · intro b k hk
    simp only [mkPower, checkExponent, hk, ↓reduceIte]
  · exact product_two_powers o me
  · intro b j k h0 h1 hm hjk
    unfold mkPower checkExponent
    by_cases hk : exponentBound me < k.natAbs
    · simp only [hk, ↓reduceIte]
    simp [hk, Term.isCondition, h0, h1, distributedPower, mergedPower, mergePowers, hm,
      checkExponent, hjk, limit_bind]
  · intro b k hb hk
    rw [mkPower_div_iff, zeroBase_iff hb]
    exact ⟨fun h => h.2, fun h => ⟨hk, h⟩⟩
  · intro a b _ hb h1
    have : (-1 : ℤ).natAbs ≤ exponentBound me := by
      unfold exponentBound
      exact le_min h1 (by norm_num)
    rw [mkDivide_div_iff, mkPower_div_iff, zeroBase_iff hb]
    exact ⟨fun h => h.2.2, fun h => ⟨this, by omega, h⟩⟩
  · intro I a b h ρ
    exact div8 I b (-1) ((mkDivide_div_iff o me a b).1 h) ρ
  · simp [mkPower, checkExponent, Term.isCondition, ratPowOp, ratPow, FieldError.lift,
      Result.ofOutcome, Result.map]
  · intro t ht hneg
    unfold mkPower checkExponent
    simp only [Int.natAbs_zero, Nat.not_lt_zero, ↓reduceIte, ht, Bool.false_eq_true]
    split
    · simp [ratPowOp, ratPow, FieldError.lift, Result.ofOutcome, Result.map]
    · simp [powerZero, hneg, maxBases, sortedTerms, sortBy, mergeAdjacent]

end Kalyx.Proofs.Terms
