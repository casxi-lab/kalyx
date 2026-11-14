module

public import Kalyx.Statements.Terms

/-!
# Proofs of the statements about the order of terms

One theorem for each registered statement of `Kalyx.Statements.Terms` about
the total order of terms and the comparison under `maxIntegerBits`, whose type
is exactly that statement.

The order of terms is reduced to a lexicographic order. A term is written as
a list of tokens (`enc`): its rank, then its parts in the order of the walk,
each list of children closed by a marker. The order of tokens is the sum of
the orders of the parts, total when the parameters are, and the first
difference that the walk of two terms finds decides the comparison of their
tokens (`lex_enc`). So the order of terms is the lexicographic order of the
tokens read through `enc` (`cmp_eq_lex`), total (`lexCmp_total`) since `enc`
is injective: terms without a first difference are equal (`eq_of_fd`); the order of the keys of
factors follows. The walk never finds two equal rationals nor an ordering
`eq` (`Proper`), and finds no difference of a term with itself, from which
the comparison under a limit follows case by case.
-/

namespace Kalyx.Proofs.Terms

open Kalyx.Spec.Terms Kalyx.Statements.Terms

/-! ## Total comparisons -/

/-- A transitive comparison read through a map is transitive. -/
private theorem transCmp_comap {α β : Type} {c : β → β → Ordering} (h : Std.TransCmp c)
    (f : α → β) : Std.TransCmp (fun a b => c (f a) (f b)) :=
  { eq_swap := Std.OrientedCmp.eq_swap (cmp := c)
    isLE_trans := Std.TransCmp.isLE_trans (cmp := c) }

/-- A total comparison read through an injective map is total. -/
private theorem totalCmp_comap {α β : Type} {c : β → β → Ordering} (h : TotalCmp c)
    (f : α → β) (hf : Function.Injective f) : TotalCmp (fun a b => c (f a) (f b)) := by
  obtain ⟨t, l⟩ := h
  exact ⟨transCmp_comap t f,
    { compare_self := Std.ReflCmp.compare_self (cmp := c)
      eq_of_compare := fun e => hf (Std.LawfulEqCmp.eq_of_compare (cmp := c) e) }⟩

/-- The comparison of pairs by their first parts, then by their second parts,
is total. -/
private theorem totalCmp_prod {α β : Type} {c₁ : α → α → Ordering} {c₂ : β → β → Ordering}
    (h₁ : TotalCmp c₁) (h₂ : TotalCmp c₂) :
    TotalCmp (fun p q : α × β => (c₁ p.1 q.1).then (c₂ p.2 q.2)) := by
  obtain ⟨t₁, l₁⟩ := h₁
  obtain ⟨t₂, l₂⟩ := h₂
  have := transCmp_comap t₁ (Prod.fst : α × β → α)
  have := transCmp_comap t₂ (Prod.snd : α × β → β)
  refine ⟨show Std.TransCmp (compareLex (fun p q : α × β => c₁ p.1 q.1)
    (fun p q => c₂ p.2 q.2)) from inferInstance, { compare_self := ?_, eq_of_compare := ?_ }⟩
  · simp [Std.ReflCmp.compare_self]
  · intro p q e
    simp only [Ordering.then_eq_eq] at e
    exact Prod.ext (Std.LawfulEqCmp.eq_of_compare e.1) (Std.LawfulEqCmp.eq_of_compare e.2)

/-- An ordering other than `eq` decides `then`. -/
private theorem then_of_ne {x : Ordering} (h : x ≠ .eq) (y : Ordering) : x.then y = x := by
  cases x <;> simp_all

/-- `c a b` is `eq` exactly for equal arguments when `c` is total. -/
private theorem eq_iff_of_total {α : Type} {c : α → α → Ordering} (h : TotalCmp c) {a b : α} :
    c a b = .eq ↔ a = b := by
  have := h.2
  exact ⟨Std.LawfulEqCmp.eq_of_compare, fun e => e ▸ Std.ReflCmp.compare_self⟩

/-- The comparison of a sum of two types: the left side first, and each side
by its own comparison. -/
private def sumCmp {α β : Type} (c₁ : α → α → Ordering) (c₂ : β → β → Ordering) :
    α ⊕ β → α ⊕ β → Ordering
  | .inl a, .inl b => c₁ a b
  | .inl _, .inr _ => .lt
  | .inr _, .inl _ => .gt
  | .inr a, .inr b => c₂ a b

/-- The comparison of a sum of two types by total comparisons is total. -/
private theorem totalCmp_sum {α β : Type} {c₁ : α → α → Ordering} {c₂ : β → β → Ordering}
    (h₁ : TotalCmp c₁) (h₂ : TotalCmp c₂) : TotalCmp (sumCmp c₁ c₂) := by
  obtain ⟨t₁, l₁⟩ := h₁
  obtain ⟨t₂, l₂⟩ := h₂
  refine ⟨{ eq_swap := ?_, isLE_trans := ?_ }, { compare_self := ?_, eq_of_compare := ?_ }⟩
  · intro a b
    cases a <;> cases b <;> simp only [sumCmp, Ordering.swap_lt, Ordering.swap_gt] <;>
      exact Std.OrientedCmp.eq_swap
  · intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> simp only [sumCmp] at hab hbc ⊢ <;>
      first | rfl | exact Std.TransCmp.isLE_trans hab hbc | simp at hab hbc
  · intro a
    cases a <;> simp only [sumCmp, Std.ReflCmp.compare_self]
  · intro a b e
    cases a <;> cases b <;> simp only [sumCmp, reduceCtorEq] at e ⊢ <;>
      exact congrArg _ (Std.LawfulEqCmp.eq_of_compare e)

/-- `lexCmp` is the lexicographic order of the core library. -/
private theorem lexCmp_eq {α : Type} (c : α → α → Ordering) : lexCmp c = List.compareLex c := by
  funext as bs
  induction as generalizing bs with
  | nil => cases bs <;> simp [lexCmp, List.compareLex_nil_nil, List.compareLex_nil_cons]
  | cons a as ih =>
    cases bs <;> simp [lexCmp, List.compareLex_cons_nil, List.compareLex_cons_cons, ih]

/-- The lexicographic order by a total order is total. -/
public theorem lexCmp_total {α : Type} {c : α → α → Ordering} (h : TotalCmp c) :
    TotalCmp (lexCmp c) := by
  obtain ⟨t, l⟩ := h
  rw [lexCmp_eq]
  exact ⟨inferInstance, inferInstance⟩

/-- The order of natural numbers is total. -/
private theorem natCmp_total : TotalCmp (compare : ℕ → ℕ → Ordering) :=
  ⟨inferInstance, inferInstance⟩

/-- The order of integers is total. -/
private theorem intCmp_total : TotalCmp (compare : ℤ → ℤ → Ordering) :=
  ⟨inferInstance, inferInstance⟩

/-- `ratCmp` is `isLE` exactly for a first rational at most the second. -/
private theorem ratCmp_isLE (a b : ℚ) : (ratCmp a b).isLE ↔ a ≤ b := by
  unfold ratCmp
  split_ifs with h₁ h₂
  · simp [h₁.le]
  · simp [h₂]
  · simp only [Ordering.isLE_gt, Bool.false_eq_true, false_iff, not_le]
    exact lt_of_le_of_ne (not_lt.1 h₁) (Ne.symm h₂)

/-- The order of rationals by value is total. -/
public theorem ratCmp_total : TotalCmp ratCmp := by
  refine ⟨{ eq_swap := ?_, isLE_trans := ?_ }, { compare_self := ?_, eq_of_compare := ?_ }⟩
  · intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · simp [ratCmp, h, not_lt.2 h.le, h.ne']
    · simp [ratCmp]
    · simp [ratCmp, h, not_lt.2 h.le, h.ne']
  · intro a b c hab hbc
    exact (ratCmp_isLE a c).2 (le_trans ((ratCmp_isLE a b).1 hab) ((ratCmp_isLE b c).1 hbc))
  · intro a
    simp [ratCmp]
  · intro a b e
    unfold ratCmp at e
    split_ifs at e with h₁ h₂
    exact h₂

/-- The order of names by their UTF-8 bytes is total. -/
public theorem nameCmp_total : TotalCmp nameCmp := by
  have := totalCmp_comap (lexCmp_total (totalCmp_comap natCmp_total UInt8.toNat
      (fun _ _ h => UInt8.toNat_inj.1 h))) (fun s : String => s.toByteArray.data.toList)
    (fun _ _ h => String.toByteArray_inj.1 (ByteArray.ext (Array.toList_inj.1 h)))
  exact this

/-- The order of the classes of calls is total. -/
public theorem callClassCmp_total : TotalCmp CallClass.cmp := by
  have := totalCmp_comap natCmp_total (fun k : CallClass => match k with
    | .registered => 0 | .formal => 1) (by intro a b h; cases a <;> cases b <;> simp_all)
  have e : CallClass.cmp = fun a b : CallClass => compare (match a with
    | .registered => 0 | .formal => 1) (match b with | .registered => 0 | .formal => 1) := by
    funext a b
    cases a <;> cases b <;> rfl
  rw [e]
  exact this

/-- The order of the identities of algebraic constants is total when the
order of coefficient lists is. -/
private theorem algebraicIdCmp_total (o : Orders) (h : TotalCmp o.coefficients) :
    TotalCmp (AlgebraicId.cmp o) := by
  have := totalCmp_comap (totalCmp_prod natCmp_total (totalCmp_prod h natCmp_total))
    (fun x : AlgebraicId => (x.minimal.length, x.minimal, x.index))
    (by intro x y e; cases x; cases y; simp_all)
  exact this

/-- A constant as a name, a real identity or a complex identity. -/
private def constantView : Constant → String ⊕ AlgebraicId ⊕ AlgebraicId
  | .named c => .inl c.name
  | .real x => .inr (.inl x)
  | .complex x => .inr (.inr x)

/-- The order of constants is total when the parameters are. -/
public theorem constantCmp_total (o : Orders) (h : o.Total) : TotalCmp (Constant.cmp o) := by
  have := totalCmp_comap (totalCmp_sum nameCmp_total
    (totalCmp_sum (algebraicIdCmp_total o h.2.2.2) (algebraicIdCmp_total o h.2.2.2)))
    constantView (by
      intro a b e
      cases a <;> cases b <;>
        simp only [constantView, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at e
      all_goals try rw [e]
      rename_i c d
      cases c <;> cases d <;> simp_all [NamedConstant.name])
  have e : Constant.cmp o = fun c d => sumCmp nameCmp
      (sumCmp (AlgebraicId.cmp o) (AlgebraicId.cmp o)) (constantView c) (constantView d) := by
    funext c d
    cases c <;> cases d <;> rfl
  rw [e]
  exact this

/-- The relation or the property of a shape of conditions. -/
private def shapeView : CondShape → Relation ⊕ String ⊕ Unit
  | .comparison r => .inl r
  | .predicate p => .inr (.inl p)
  | _ => .inr (.inr ())

/-- The order of the shapes of conditions is total when the parameters are. -/
public theorem condShapeCmp_total (o : Orders) (h : o.Total) : TotalCmp (CondShape.cmp o) := by
  have hu : TotalCmp (fun _ _ : Unit => Ordering.eq) :=
    ⟨{ eq_swap := rfl, isLE_trans := fun _ _ => rfl },
      { compare_self := rfl, eq_of_compare := fun _ => rfl }⟩
  have := totalCmp_comap (totalCmp_prod h.1 (totalCmp_sum h.2.1 (totalCmp_sum h.2.2.1 hu)))
    (fun s : CondShape => (s.kind, shapeView s))
    (by intro a b e; cases a <;> cases b <;> simp_all [CondShape.kind, shapeView])
  have e : CondShape.cmp o = fun s r => (o.shapes s.kind r.kind).then (sumCmp o.relations
      (sumCmp o.properties (fun _ _ : Unit => Ordering.eq)) (shapeView s) (shapeView r)) := by
    funext s r
    have := h.1.2
    by_cases hk : s.kind = r.kind
    · cases s <;> cases r <;> first | rfl | (exfalso; simp [CondShape.kind] at hk)
    · have hne : o.shapes s.kind r.kind ≠ .eq := fun e => hk (Std.LawfulEqCmp.eq_of_compare e)
      unfold CondShape.cmp
      rw [then_of_ne hne, then_of_ne hne]
  rw [e]
  exact this

/-! ## Terms as lists of tokens -/

/-- The parts that the walk of two terms compares, as tokens: ranks and the
markers of lists, rationals, constants, names, classes of calls, exponents and
shapes of conditions. -/
private abbrev Tok := ℕ ⊕ ℚ ⊕ Constant ⊕ String ⊕ CallClass ⊕ ℤ ⊕ CondShape

/-- The order of tokens: of two tokens of one kind, the order of their parts. -/
private def tokCmp (o : Orders) : Tok → Tok → Ordering :=
  sumCmp compare (sumCmp ratCmp (sumCmp (Constant.cmp o) (sumCmp nameCmp
    (sumCmp CallClass.cmp (sumCmp compare (CondShape.cmp o))))))

/-- The order of tokens is total when the parameters are. -/
private theorem tokCmp_total (o : Orders) (h : o.Total) : TotalCmp (tokCmp o) :=
  totalCmp_sum natCmp_total (totalCmp_sum ratCmp_total (totalCmp_sum (constantCmp_total o h)
    (totalCmp_sum nameCmp_total (totalCmp_sum callClassCmp_total
      (totalCmp_sum intCmp_total (condShapeCmp_total o h))))))

/-- A rank or a marker. -/
private abbrev tN (n : ℕ) : Tok := .inl n
/-- A rational. -/
private abbrev tQ (q : ℚ) : Tok := .inr (.inl q)
/-- A constant. -/
private abbrev tC (c : Constant) : Tok := .inr (.inr (.inl c))
/-- A name. -/
private abbrev tS (s : String) : Tok := .inr (.inr (.inr (.inl s)))
/-- A class of calls. -/
private abbrev tK (k : CallClass) : Tok := .inr (.inr (.inr (.inr (.inl k))))
/-- An exponent. -/
private abbrev tZ (k : ℤ) : Tok := .inr (.inr (.inr (.inr (.inr (.inl k)))))
/-- A shape of conditions. -/
private abbrev tH (s : CondShape) : Tok := .inr (.inr (.inr (.inr (.inr (.inr s)))))

/-- Two ranks or markers compare as natural numbers. -/
private theorem tokCmp_N (o : Orders) (a b : ℕ) : tokCmp o (tN a) (tN b) = compare a b := rfl
/-- Two rationals compare by value. -/
private theorem tokCmp_Q (o : Orders) (a b : ℚ) : tokCmp o (tQ a) (tQ b) = ratCmp a b := rfl
/-- Two constants compare by `Constant.cmp`. -/
private theorem tokCmp_C (o : Orders) (a b : Constant) :
    tokCmp o (tC a) (tC b) = Constant.cmp o a b := rfl
/-- Two names compare by their bytes. -/
private theorem tokCmp_S (o : Orders) (a b : String) : tokCmp o (tS a) (tS b) = nameCmp a b :=
  rfl
/-- Two classes of calls compare by `CallClass.cmp`. -/
private theorem tokCmp_K (o : Orders) (a b : CallClass) : tokCmp o (tK a) (tK b) = a.cmp b :=
  rfl
/-- Two exponents compare as integers. -/
private theorem tokCmp_Z (o : Orders) (a b : ℤ) : tokCmp o (tZ a) (tZ b) = compare a b := rfl
/-- Two shapes compare by `CondShape.cmp`. -/
private theorem tokCmp_H (o : Orders) (a b : CondShape) :
    tokCmp o (tH a) (tH b) = CondShape.cmp o a b := rfl
/-- The marker of the end of a list comes first. -/
private theorem compare_zero_one : compare (0 : ℕ) 1 = .lt := by decide
/-- The marker of a further element comes last. -/
private theorem compare_one_zero : compare (1 : ℕ) 0 = .gt := by decide

mutual

/-- A term as tokens: its rank, then its parts in the order of the walk. -/
private def enc : Term → List Tok
  | .number a => [tN 0, tQ a]
  | .constant c => [tN 1, tC c]
  | .symbol s => [tN 2, tS s]
  | .call h as => tN 3 :: tS h.name :: tK h.callClass :: encList as
  | .power b k => tN 4 :: (enc b ++ [tZ k])
  | .product a fs => tN 5 :: (encList fs ++ [tQ a])
  | .sum a ms => tN 6 :: (encPairs ms ++ [tQ a])
  | .condition s xs => tN 7 :: tH s :: encList xs
  termination_by structural t => t

/-- A list of terms as tokens: each term after the marker 1, then the marker 0. -/
private def encList : List Term → List Tok
  | [] => [tN 0]
  | t :: ts => tN 1 :: (enc t ++ encList ts)
  termination_by structural ts => ts

/-- A list of monomials as tokens: each core and coefficient after the marker
1, then the marker 0. -/
private def encPairs : List (ℚ × Term) → List Tok
  | [] => [tN 0]
  | (a, t) :: ms => tN 1 :: (enc t ++ tQ a :: encPairs ms)
  termination_by structural ms => ms

end

/-- The tokens of a term start with its rank. -/
private theorem enc_head (t : Term) : ∃ l, enc t = tN t.rank :: l := by
  cases t <;> simp [enc, Term.rank]

/-! ## The first difference -/

/-- A difference that the walk can find: two rationals that differ, or an
ordering other than `eq`. -/
private def Proper : Difference → Prop
  | .equal => True
  | .rationals a b => a ≠ b
  | .other r => r ≠ .eq

/-- `ratCmp` is `eq` exactly for equal rationals. -/
private theorem ratCmp_eq_iff (a b : ℚ) : ratCmp a b = .eq ↔ a = b :=
  eq_iff_of_total ratCmp_total

/-- The first of two proper differences is proper. -/
private theorem proper_andThen {d e : Difference} (hd : Proper d) (he : Proper e) :
    Proper (d.andThen e) := by
  cases d <;> simp_all [Difference.andThen]

/-- The difference of two parts is proper. -/
private theorem proper_ofOrdering (r : Ordering) : Proper (.ofOrdering r) := by
  cases r <;> simp [Difference.ofOrdering, Proper]

/-- The difference of two rationals is proper. -/
private theorem proper_ofRationals (a b : ℚ) : Proper (.ofRationals a b) := by
  unfold Difference.ofRationals
  split <;> simp_all [Proper]

/-- The first difference of two terms is proper. -/
private theorem proper_fd (o : Orders) : ∀ s t, Proper (Term.firstDifference o s t) := by
  apply Term.firstDifference.induct_unfolding o (motive_1 := fun _ _ d => Proper d)
    (motive_2 := fun _ _ d => Proper d) (motive_3 := fun _ _ d => Proper d)
  all_goals intros
  all_goals repeat' first | assumption | apply proper_andThen | exact proper_ofOrdering _ |
    exact proper_ofRationals _ _ | simp [Proper]

/-- The first difference of two lists of terms is proper. -/
private theorem proper_fdList (o : Orders) :
    ∀ as bs, Proper (Term.firstDifferenceList o as bs) := by
  apply Term.firstDifferenceList.induct_unfolding o (motive_1 := fun _ _ d => Proper d)
    (motive_2 := fun _ _ d => Proper d) (motive_3 := fun _ _ d => Proper d)
  all_goals intros
  all_goals repeat' first | assumption | apply proper_andThen | exact proper_ofOrdering _ |
    exact proper_ofRationals _ _ | simp [Proper]

/-- The first difference of two lists of monomials is proper. -/
private theorem proper_fdPairs (o : Orders) :
    ∀ ms ns, Proper (Term.firstDifferencePairs o ms ns) := by
  apply Term.firstDifferencePairs.induct_unfolding o (motive_1 := fun _ _ d => Proper d)
    (motive_2 := fun _ _ d => Proper d) (motive_3 := fun _ _ d => Proper d)
  all_goals intros
  all_goals repeat' first | assumption | apply proper_andThen | exact proper_ofOrdering _ |
    exact proper_ofRationals _ _ | simp [Proper]

/-- The ordering of the first of two differences, the first proper. -/
private theorem order_andThen {d : Difference} (h : Proper d) (e : Difference) :
    (d.andThen e).order = d.order.then e.order := by
  cases d with
  | equal => rfl
  | rationals a b => exact (then_of_ne (fun e => h ((ratCmp_eq_iff a b).1 e)) _).symm
  | other r => exact (then_of_ne h _).symm

/-- No difference orders `eq`. -/
private theorem order_equal : Difference.equal.order = .eq := rfl

/-- Two other parts order as they compare. -/
private theorem order_other (r : Ordering) : (Difference.other r).order = r := rfl

/-- The ordering of the difference of two parts. -/
private theorem order_ofOrdering (r : Ordering) : (Difference.ofOrdering r).order = r := by
  cases r <;> rfl

/-- The ordering of the difference of two rationals. -/
private theorem order_ofRationals (a b : ℚ) :
    (Difference.ofRationals a b).order = ratCmp a b := by
  unfold Difference.ofRationals
  split
  · rename_i h
    subst h
    exact ((ratCmp_eq_iff _ _).2 rfl).symm
  · rfl

/-- A proper difference orders `eq` exactly when it is none. -/
private theorem order_eq_eq {d : Difference} (h : Proper d) : d.order = .eq ↔ d = .equal := by
  cases d with
  | equal => simp [Difference.order]
  | rationals a b => simpa [Difference.order, ratCmp_eq_iff, Proper] using h
  | other r => simpa [Difference.order, Proper] using h

/-- No difference of two parts exactly for parts that compare `eq`. -/
private theorem ofOrdering_eq_equal (r : Ordering) :
    Difference.ofOrdering r = .equal ↔ r = .eq := by
  cases r <;> simp [Difference.ofOrdering]

/-- No difference of two rationals exactly for equal rationals. -/
private theorem ofRationals_eq_equal (a b : ℚ) :
    Difference.ofRationals a b = .equal ↔ a = b := by
  unfold Difference.ofRationals
  split <;> simp_all

/-- No first difference of two pairs exactly when neither pair differs. -/
private theorem andThen_eq_equal (d e : Difference) :
    d.andThen e = .equal ↔ d = .equal ∧ e = .equal := by
  cases d <;> simp [Difference.andThen]

/-- Heads are equal exactly when their names and their classes are. -/
private theorem head_eq_iff (h g : Head) :
    h = g ↔ h.name = g.name ∧ h.callClass = g.callClass := by
  cases h
  cases g
  simp

/-- Terms that the walk does not match by kind differ in rank. -/
private theorem rank_ne {t u : Term}
    (h₁ : ∀ a b, t = .number a → u = .number b → False)
    (h₂ : ∀ c d, t = .constant c → u = .constant d → False)
    (h₃ : ∀ a b, t = .symbol a → u = .symbol b → False)
    (h₄ : ∀ h as g bs, t = .call h as → u = .call g bs → False)
    (h₅ : ∀ b k c l, t = .power b k → u = .power c l → False)
    (h₆ : ∀ a fs b gs, t = .product a fs → u = .product b gs → False)
    (h₇ : ∀ a ms b ns, t = .sum a ms → u = .sum b ns → False)
    (h₈ : ∀ s xs r ys, t = .condition s xs → u = .condition r ys → False) :
    t.rank ≠ u.rank := by
  cases t <;> cases u <;> simp only [Term.rank] <;> first | decide | (exfalso; first
    | exact h₁ _ _ rfl rfl | exact h₂ _ _ rfl rfl | exact h₃ _ _ rfl rfl
    | exact h₄ _ _ _ _ rfl rfl | exact h₅ _ _ _ _ rfl rfl | exact h₆ _ _ _ _ rfl rfl
    | exact h₇ _ _ _ _ rfl rfl | exact h₈ _ _ _ _ rfl rfl)

/-- The tokens of two terms, each followed by more tokens, compare by the
first difference of the terms, then by the tokens that follow. -/
private theorem lex_enc (o : Orders) : ∀ s t (x y : List Tok),
    lexCmp (tokCmp o) (enc s ++ x) (enc t ++ y) =
      (Term.firstDifference o s t).order.then (lexCmp (tokCmp o) x y) := by
  apply Term.firstDifference.induct_unfolding o
    (motive_1 := fun s t d => ∀ x y, lexCmp (tokCmp o) (enc s ++ x) (enc t ++ y) =
      d.order.then (lexCmp (tokCmp o) x y))
    (motive_2 := fun ms ns d => ∀ x y,
      lexCmp (tokCmp o) (encPairs ms ++ x) (encPairs ns ++ y) =
        d.order.then (lexCmp (tokCmp o) x y))
    (motive_3 := fun as bs d => ∀ x y,
      lexCmp (tokCmp o) (encList as ++ x) (encList bs ++ y) =
        d.order.then (lexCmp (tokCmp o) x y))
  rotate_left 8
  · intro t u h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ x y
    have hne : compare t.rank u.rank ≠ .eq := fun e =>
      rank_ne h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ (Nat.compare_eq_eq.1 e)
    obtain ⟨l, hl⟩ := enc_head t
    obtain ⟨l', hl'⟩ := enc_head u
    rw [hl, hl', order_ofOrdering]
    simp only [List.cons_append, lexCmp, tokCmp, sumCmp]
    rw [then_of_ne hne, then_of_ne hne]
  all_goals intros
  all_goals simp only [enc, encList, encPairs, List.cons_append, List.nil_append,
    List.append_assoc, lexCmp, tokCmp_N, tokCmp_Q, tokCmp_C, tokCmp_S, tokCmp_K, tokCmp_Z,
    tokCmp_H, compare_zero_one, compare_one_zero, Std.ReflCmp.compare_self, Ordering.eq_then,
    Ordering.lt_then, Ordering.gt_then, order_ofRationals, order_ofOrdering, order_equal,
    order_other, order_andThen, proper_fd, proper_fdList, proper_fdPairs, proper_ofOrdering,
    proper_ofRationals, proper_andThen, Ordering.then_assoc, *]

/-- The order of terms is the order of their tokens. -/
private theorem cmp_eq_lex (o : Orders) (s t : Term) :
    Term.cmp o s t = lexCmp (tokCmp o) (enc s) (enc t) := by
  have := lex_enc o s t [] []
  simp only [List.append_nil, lexCmp, Ordering.then_eq] at this
  exact this.symm

/-- Two terms without a first difference are equal, when the parameters are
total. -/
private theorem eq_of_fd (o : Orders) (ho : o.Total) :
    ∀ s t, Term.firstDifference o s t = .equal → s = t := by
  apply Term.firstDifference.induct_unfolding o (motive_1 := fun s t d => d = .equal → s = t)
    (motive_2 := fun ms ns d => d = .equal → ms = ns)
    (motive_3 := fun as bs d => d = .equal → as = bs)
  rotate_left 8
  · intro t u h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ e
    rw [ofOrdering_eq_equal, Nat.compare_eq_eq] at e
    exact absurd e (rank_ne h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈)
  all_goals intros
  all_goals simp_all [ofOrdering_eq_equal, ofRationals_eq_equal, andThen_eq_equal, head_eq_iff,
    eq_iff_of_total nameCmp_total, eq_iff_of_total callClassCmp_total,
    eq_iff_of_total (constantCmp_total o ho), eq_iff_of_total (condShapeCmp_total o ho)]

/-! ## The order of terms -/

/-- The order of terms is total when the parameters are. -/
public theorem termCmp_total (o : Orders) (h : o.Total) : TotalCmp (Term.cmp o) := by
  have ht := lexCmp_total (tokCmp_total o h)
  have e : Term.cmp o = fun s t => lexCmp (tokCmp o) (enc s) (enc t) :=
    funext fun s => funext fun t => cmp_eq_lex o s t
  rw [e]
  refine totalCmp_comap ht enc fun s t est => eq_of_fd o h s t ?_
  rw [← order_eq_eq (proper_fd o s t)]
  change Term.cmp o s t = .eq
  rw [cmp_eq_lex, est]
  exact (eq_iff_of_total ht).2 rfl

/-- The order of the keys of factors is total when the parameters are. -/
public theorem keyCmp_total (o : Orders) (h : o.Total) : TotalCmp (Key.cmp o) := by
  have := totalCmp_comap (totalCmp_prod (termCmp_total o h) natCmp_total)
    (fun x : Key => (x.base, x.negative.toNat)) (by
      rintro ⟨b, n⟩ ⟨c, m⟩ e
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, e⟩ := e
      cases n <;> cases m <;> simp_all)
  exact this

/-- Terms of a lower rank come first. -/
public theorem termCmp_lt_of_rank_lt (o : Orders) {s t : Term} (h : s.rank < t.rank) :
    Term.cmp o s t = .lt := by
  obtain ⟨l, hl⟩ := enc_head s
  obtain ⟨l', hl'⟩ := enc_head t
  rw [cmp_eq_lex, hl, hl', lexCmp, tokCmp_N, Nat.compare_eq_lt.2 h, Ordering.lt_then]

/-- A term has no first difference with itself, when the parameters are
total. -/
public theorem firstDifference_self (o : Orders) (h : o.Total) (s : Term) :
    Term.firstDifference o s s = .equal :=
  (order_eq_eq (proper_fd o s s)).1 ((eq_iff_of_total (termCmp_total o h)).2 rfl)

/-- The first difference of the walk is never two equal rationals. -/
public theorem firstDifference_rationals_ne (o : Orders) {s t : Term} {a b : ℚ}
    (h : Term.firstDifference o s t = .rationals a b) : a ≠ b := by
  have := proper_fd o s t
  rw [h] at this
  exact this

/-! ## The statements -/

/-- Proves `TermOrderIsTotal`: the orders of terms and of keys are total, and
a lower rank comes first. -/
public theorem termOrderIsTotal : TermOrderIsTotal :=
  fun o h => ⟨termCmp_total o h, keyCmp_total o h, fun _ _ => termCmp_lt_of_rank_lt o⟩

/-- Proves `ComparisonUnderBitLimit`, by the cases of the first difference:
none, two rationals, or two other parts. -/
public theorem comparisonUnderBitLimit : ComparisonUnderBitLimit := by
  intro o m s t ho
  have hs : s = t → Term.firstDifference o s t = .equal := by
    rintro rfl
    exact firstDifference_self o ho s
  unfold Term.compareAt Term.cmp
  cases hd : Term.firstDifference o s t with
  | equal => simp [Difference.order]
  | other r =>
    rw [hd] at hs
    simp_all [Difference.order]
  | rationals a b =>
    rw [hd] at hs
    dsimp only
    unfold ratCompareAt
    refine ⟨fun e => ?_, fun r => ?_, fun e => absurd (hs e) (by simp), fun f => ?_,
      fun H => ?_⟩ <;> split
    · simp
    · simp
    · simp
    · rintro ⟨⟩
      rfl
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      rintro ⟨⟩
      exact ⟨rfl, a, b, rfl, firstDifference_rationals_ne o hd, hc.2⟩
    · simp
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have := H a b rfl
      omega
    · rfl

end Kalyx.Proofs.Terms
