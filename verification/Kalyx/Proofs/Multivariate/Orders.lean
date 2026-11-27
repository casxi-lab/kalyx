module

public import Kalyx.Statements.Multivariate

/-!
# Proofs of the statements about the monomial orders

One theorem for each registered statement of `Kalyx.Statements.Multivariate`
about the monomial orders, whose type is exactly that statement.

Each computable comparison agrees with its strict order (`Orders.Agree`): the
comparisons of `lex` and of the reverse lexicographic order by recursion on the
number of variables, which compares the first or the last variable first, and
those of `grlex`, `grevlex` and the block orders as lexicographic products
(`Orders.Agree.then`) of agreeing comparisons. Irreflexivity and trichotomy
follow from the agreement. Transitivity, compatibility with the product of
monomials and well-foundedness are proved order by order, the last for the
graded orders through the finitely many vectors of each total degree, and no
vector is below the constant one, so every other vector is above it. A block
order eliminates its first block by `grevlex` on that block, and the block
orders of the splits 0 and `n` compare as `grevlex` once their empty block is
dropped. Each order is the strict order of a monomial order of Mathlib
(`Orders.toMathlib`), whose type is the exponent vectors ordered by it.
-/

namespace Kalyx.Proofs.Multivariate

open Kalyx.Spec.Multivariate Kalyx.Statements.Multivariate

namespace Orders

/-! ## Comparisons that agree with strict orders -/

/-- The comparison `c` agrees with the strict order `r`. -/
def Agree {α : Type} (c : α → α → Ordering) (r : α → α → Prop) : Prop :=
  ∀ a b, (c a b = .lt ↔ r a b) ∧ (c a b = .eq ↔ a = b) ∧ (c a b = .gt ↔ r b a)

section Agree

variable {α β : Type} {c : α → α → Ordering} {r : α → α → Prop}

/-- A relation with an agreeing comparison is irreflexive. -/
theorem Agree.irrefl (h : Agree c r) (a : α) : ¬r a a := fun hr => by
  have := (h a a).1.mpr hr
  rw [(h a a).2.1.mpr rfl] at this
  cases this

/-- A relation with an agreeing comparison is trichotomous. -/
theorem Agree.trichotomous (h : Agree c r) (a b : α) : r a b ∨ a = b ∨ r b a := by
  obtain ⟨l, e, g⟩ := h a b
  cases hc : c a b
  exacts [.inl (l.mp hc), .inr (.inl (e.mp hc)), .inr (.inr (g.mp hc))]

/-- Agreement is kept along an injective map. -/
theorem Agree.comap (h : Agree c r) {f : β → α} (hf : Function.Injective f) :
    Agree (fun a b => c (f a) (f b)) (fun a b => r (f a) (f b)) :=
  fun _ _ => ⟨(h _ _).1, (h _ _).2.1.trans hf.eq_iff, (h _ _).2.2⟩

/-- Agreement is kept when the relation is replaced by an equivalent one. -/
theorem Agree.of_iff {s : α → α → Prop} (h : Agree c r) (hs : ∀ a b, r a b ↔ s a b) :
    Agree c s :=
  fun a b => by rw [← hs, ← hs]; exact h a b

/-- `Ordering.then` of two agreeing comparisons agrees with the lexicographic product. -/
theorem Agree.then {c' : β → β → Ordering} {r' : β → β → Prop} (h : Agree c r)
    (h' : Agree c' r') :
    Agree (fun p q : α × β => (c p.1 q.1).then (c' p.2 q.2)) (Prod.Lex r r') := by
  rintro ⟨a, a'⟩ ⟨b, b'⟩
  obtain ⟨l, e, g⟩ := h a b
  obtain ⟨l', e', g'⟩ := h' a' b'
  simp only [Prod.lex_def, Prod.mk.injEq, Ordering.then_eq_lt, Ordering.then_eq_eq,
    Ordering.then_eq_gt, l, e, g, l', e', g', eq_comm (a := b), and_self]

/-- `compare` agrees with `<` on the natural numbers. -/
theorem agree_nat : Agree (compare : ℕ → ℕ → Ordering) (· < ·) :=
  fun _ _ => ⟨Nat.compare_eq_lt, Nat.compare_eq_eq, Nat.compare_eq_gt⟩

/-- The swapped `compare` agrees with `>` on the natural numbers. -/
theorem agree_nat_swap : Agree (fun a b : ℕ => compare b a) (fun a b => b < a) :=
  fun _ _ => ⟨Nat.compare_eq_lt, Nat.compare_eq_eq.trans eq_comm, Nat.compare_eq_gt⟩

end Agree

/-- `Prod.Lex` of two transitive relations is transitive. -/
theorem prodLex_trans {α β : Type} {r : α → α → Prop} {s : β → β → Prop} {x y z : α × β}
    (h₁ : Prod.Lex r s x y) (h₂ : Prod.Lex r s y z) (hr : ∀ {a b c}, r a b → r b c → r a c)
    (hs : ∀ {a b c}, s a b → s b c → s a c) : Prod.Lex r s x z := by
  rw [Prod.lex_def] at *
  rcases h₁ with h₁ | ⟨e₁, h₁⟩ <;> rcases h₂ with h₂ | ⟨e₂, h₂⟩
  · exact .inl (hr h₁ h₂)
  · exact .inl (e₂ ▸ h₁)
  · exact .inl (e₁ ▸ h₂)
  · exact .inr ⟨e₁.trans e₂, hs h₁ h₂⟩

/-! ## `lex` and the reverse lexicographic order, variable by variable -/

/-- On vectors of no variables, a constant `eq` agrees with an empty relation. -/
theorem agree_zero {c : Exponents 0 → Exponents 0 → Ordering}
    {r : Exponents 0 → Exponents 0 → Prop} (hc : ∀ a b, c a b = .eq) (hr : ∀ a b, ¬r a b) :
    Agree c r := fun a b => by
  simp [hc, hr, Subsingleton.elim a b]

variable {n : ℕ}

/-- A vector is determined by its first exponent and the others. -/
theorem cons_injective : Function.Injective fun a : Exponents (n + 1) => (a 0, Fin.tail a) :=
  fun a b h => funext fun i => Fin.cases (motive := fun i => a i = b i) (congrArg Prod.fst h)
    (fun j => congrFun (congrArg Prod.snd h) j) i

/-- A vector is determined by its last exponent and the others. -/
theorem snoc_injective :
    Function.Injective fun a : Exponents (n + 1) => (a (Fin.last n), Fin.init a) :=
  fun a b h => funext fun i => Fin.lastCases (motive := fun i => a i = b i)
    (congrArg Prod.fst h) (fun j => congrFun (congrArg Prod.snd h) j) i

/-- `lex` compares the first exponent, then the others. -/
theorem lexLT_succ {a b : Exponents (n + 1)} :
    LexLT a b ↔ Prod.Lex (· < ·) LexLT (a 0, Fin.tail a) (b 0, Fin.tail b) := by
  rw [Prod.lex_def]
  constructor
  · rintro ⟨j, hj, h⟩
    cases j using Fin.cases with
    | zero => exact .inl h
    | succ j =>
      exact .inr ⟨hj 0 j.succ_pos, j, fun d hd => hj d.succ (Fin.succ_lt_succ_iff.mpr hd), h⟩
  · rintro (h | ⟨h₀, j, hj, h⟩)
    · exact ⟨0, fun d hd => absurd hd (Fin.not_lt_zero d), h⟩
    · refine ⟨j.succ, fun d hd => ?_, h⟩
      cases d using Fin.cases with
      | zero => exact h₀
      | succ d => exact hj d (Fin.succ_lt_succ_iff.mp hd)

/-- The reverse lexicographic order compares the last exponent, then the others. -/
theorem revLexLT_succ {a b : Exponents (n + 1)} :
    RevLexLT a b ↔ Prod.Lex (fun x y => y < x) RevLexLT (a (Fin.last n), Fin.init a)
      (b (Fin.last n), Fin.init b) := by
  rw [Prod.lex_def]
  constructor
  · rintro ⟨j, hj, h⟩
    cases j using Fin.lastCases with
    | last => exact .inl h
    | cast j =>
      exact .inr ⟨hj _ (Fin.castSucc_lt_last j), j,
        fun d hd => hj d.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hd), h⟩
  · rintro (h | ⟨h₀, j, hj, h⟩)
    · exact ⟨Fin.last n, fun d hd => absurd hd (not_lt.mpr d.le_last), h⟩
    · refine ⟨j.castSucc, fun d hd => ?_, h⟩
      cases d using Fin.lastCases with
      | last => exact h₀
      | cast d => exact hj d (Fin.castSucc_lt_castSucc_iff.mp hd)

/-- `compareLex` agrees with `LexLT`. -/
theorem agree_lex : ∀ n, Agree (compareLex (n := n)) LexLT
  | 0 => agree_zero (fun _ _ => rfl) fun _ _ ⟨j, _⟩ => j.elim0
  | n + 1 => ((agree_nat.then (agree_lex n)).comap cons_injective).of_iff
    fun _ _ => lexLT_succ.symm

/-- `compareRevLex` agrees with `RevLexLT`. -/
theorem agree_revLex : ∀ n, Agree (compareRevLex (n := n)) RevLexLT
  | 0 => agree_zero (fun _ _ => rfl) fun _ _ ⟨j, _⟩ => j.elim0
  | n + 1 => ((agree_nat_swap.then (agree_revLex n)).comap snoc_injective).of_iff
    fun _ _ => revLexLT_succ.symm

/-- `LexLT` is transitive. -/
theorem lexLT_trans : ∀ {n} {a b c : Exponents n}, LexLT a b → LexLT b c → LexLT a c
  | 0, _, _, _, ⟨j, _⟩, _ => j.elim0
  | _ + 1, _, _, _, h₁, h₂ => lexLT_succ.mpr
    (prodLex_trans (lexLT_succ.mp h₁) (lexLT_succ.mp h₂) Nat.lt_trans lexLT_trans)

/-- `RevLexLT` is transitive. -/
theorem revLexLT_trans : ∀ {n} {a b c : Exponents n}, RevLexLT a b → RevLexLT b c → RevLexLT a c
  | 0, _, _, _, ⟨j, _⟩, _ => j.elim0
  | _ + 1, _, _, _, h₁, h₂ => revLexLT_succ.mpr (prodLex_trans (revLexLT_succ.mp h₁)
    (revLexLT_succ.mp h₂) (fun h₁ h₂ => Nat.lt_trans h₂ h₁) revLexLT_trans)

/-- `LexLT` is well founded. -/
theorem lexLT_wf : ∀ n, WellFounded (LexLT (n := n))
  | 0 => ⟨fun a => ⟨a, fun _ ⟨j, _⟩ => j.elim0⟩⟩
  | n + 1 => (InvImage.wf (fun a : Exponents (n + 1) => (a 0, Fin.tail a))
    (wellFounded_lt.prod_lex (lexLT_wf n))).mono fun _ _ h => lexLT_succ.mp h

/-- `LexLT` is compatible with the product of monomials and cancellative. -/
theorem lexLT_product {a b c : Exponents n} : LexLT a b ↔ LexLT (a.product c) (b.product c) := by
  simp only [LexLT, Exponents.product, add_left_inj, add_lt_add_iff_right]

/-- `RevLexLT` is compatible with the product of monomials and cancellative. -/
theorem revLexLT_product {a b c : Exponents n} :
    RevLexLT a b ↔ RevLexLT (a.product c) (b.product c) := by
  simp only [RevLexLT, Exponents.product, add_left_inj, add_lt_add_iff_right]

/-! ## Graded orders -/

/-- The degree of a product is the sum of the degrees. -/
theorem degree_product (a b : Exponents n) : (a.product b).degree = a.degree + b.degree :=
  Finset.sum_add_distrib

/-- Only the constant vector has degree 0. -/
theorem degree_eq_zero {a : Exponents n} : a.degree = 0 ↔ a = Exponents.constant := by
  simp [Exponents.degree, Finset.sum_eq_zero_iff, funext_iff, Exponents.constant]

/-- The vectors of one total degree are finitely many. -/
theorem finite_degree_eq (n d : ℕ) : {a : Exponents n | a.degree = d}.Finite :=
  (Set.Finite.pi' fun _ => Set.finite_Iic d).subset fun a ha i =>
    (Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)).trans_eq ha

/-- A vector is determined by its degree and itself. -/
theorem graded_injective : Function.Injective fun a : Exponents n => (a.degree, a) :=
  fun _ _ h => congrArg Prod.snd h

/-- A graded order of a strict order is well founded. -/
theorem graded_wf {s : Exponents n → Exponents n → Prop} (hirr : ∀ a, ¬s a a)
    (htr : ∀ {a b c}, s a b → s b c → s a c) :
    WellFounded fun a b : Exponents n => Prod.Lex (· < ·) s (a.degree, a) (b.degree, b) :=
  haveI : IsStrictOrder (Exponents n) s := { irrefl := hirr, trans := fun _ _ _ => htr }
  WellFounded.prod_lex_of_wellFoundedOn_fiber (rα := (· < ·)) (rβ := s)
    (f := Exponents.degree) (g := fun a => a) (InvImage.wf _ wellFounded_lt)
    fun d => (finite_degree_eq n d).wellFoundedOn

/-- A graded order is compatible with the product of monomials when its second order is. -/
theorem graded_product {s : Exponents n → Exponents n → Prop}
    (hs : ∀ {a b c : Exponents n}, s a b ↔ s (a.product c) (b.product c)) {a b c : Exponents n} :
    Prod.Lex (· < ·) s (a.degree, a) (b.degree, b) ↔ Prod.Lex (· < ·) s
      ((a.product c).degree, a.product c) ((b.product c).degree, b.product c) := by
  simp only [Prod.lex_def, degree_product, add_lt_add_iff_right, add_left_inj, ← hs]

/-- No vector is below the constant one in a graded order of an irreflexive order. -/
theorem graded_not_lt_constant {s : Exponents n → Exponents n → Prop} (hs : ∀ a, ¬s a a)
    (a : Exponents n) :
    ¬Prod.Lex (· < ·) s (a.degree, a)
      ((Exponents.constant : Exponents n).degree, Exponents.constant) := by
  simp only [Prod.lex_def, degree_eq_zero.mpr rfl, Nat.not_lt_zero, false_or, not_and]
  intro h
  rw [degree_eq_zero.mp h]
  exact hs _

/-- `GrevLexLT` is transitive. -/
theorem grevLexLT_trans {a b c : Exponents n} : GrevLexLT a b → GrevLexLT b c → GrevLexLT a c :=
  fun h₁ h₂ => prodLex_trans h₁ h₂ Nat.lt_trans revLexLT_trans

/-- `GrevLexLT` is compatible with the product of monomials and cancellative. -/
theorem grevLexLT_product {a b c : Exponents n} :
    GrevLexLT a b ↔ GrevLexLT (a.product c) (b.product c) :=
  graded_product revLexLT_product

/-- `compareGrLex` agrees with `GrLexLT`. -/
theorem agree_grlex : Agree (compareGrLex (n := n)) GrLexLT :=
  (agree_nat.then (agree_lex n)).comap graded_injective

/-- `compareGrevLex` agrees with `GrevLexLT`. -/
theorem agree_grevlex : Agree (compareGrevLex (n := n)) GrevLexLT :=
  (agree_nat.then (agree_revLex n)).comap graded_injective

/-! ## Block orders -/

/-- A vector is determined by its two blocks. -/
theorem blocks_injective (k : Fin (n + 1)) :
    Function.Injective fun a : Exponents n => (a.firstBlock k, a.secondBlock k) := by
  intro a b h
  simp only [Prod.mk.injEq, funext_iff] at h
  funext i
  by_cases hi : i.val < k.val
  · exact h.1 ⟨i, hi⟩
  · have := i.isLt
    have e : Fin.cast (Nat.add_sub_cancel' (Nat.le_of_lt_succ k.isLt))
        (Fin.natAdd k ⟨i - k, by omega⟩) = i := Fin.ext (show (k : ℕ) + (i - k) = i by omega)
    rw [← e]
    exact h.2 _

/-- The first block of a product is the product of the first blocks. -/
theorem firstBlock_product (k : Fin (n + 1)) (a b : Exponents n) :
    (a.product b).firstBlock k = (a.firstBlock k).product (b.firstBlock k) := rfl

/-- The second block of a product is the product of the second blocks. -/
theorem secondBlock_product (k : Fin (n + 1)) (a b : Exponents n) :
    (a.product b).secondBlock k = (a.secondBlock k).product (b.secondBlock k) := rfl

/-- The product of monomials is cancellative. -/
theorem product_right_cancel {a b c : Exponents n} : a.product c = b.product c ↔ a = b := by
  simp [Exponents.product, funext_iff]

/-- `compareBlock` agrees with `BlockLT`. -/
theorem agree_block (k : Fin (n + 1)) : Agree (compareBlock k) (BlockLT k) :=
  (agree_grevlex.then agree_grevlex).comap (blocks_injective k)

/-! ## The four orders -/

/-- Each comparison agrees with its strict order. -/
theorem agree : ∀ o : OrderKind n, Agree o.compare o.Lt
  | .lex => agree_lex n
  | .grlex => agree_grlex
  | .grevlex => agree_grevlex
  | .block k => agree_block k

/-- Each strict order is transitive. -/
theorem orderTrans : ∀ (o : OrderKind n) {a b c : Exponents n}, o.Lt a b → o.Lt b c → o.Lt a c
  | .lex, _, _, _ => lexLT_trans
  | .grlex, _, _, _ => fun h₁ h₂ => prodLex_trans h₁ h₂ Nat.lt_trans lexLT_trans
  | .grevlex, _, _, _ => grevLexLT_trans
  | .block _, _, _, _ => fun h₁ h₂ => prodLex_trans h₁ h₂ grevLexLT_trans grevLexLT_trans

/-- Each strict order is well founded. -/
theorem orderWf : ∀ o : OrderKind n, WellFounded o.Lt
  | .lex => lexLT_wf n
  | .grlex => graded_wf (agree_lex n).irrefl lexLT_trans
  | .grevlex => graded_wf (agree_revLex n).irrefl revLexLT_trans
  | .block k => InvImage.wf (fun a : Exponents n => (a.firstBlock k, a.secondBlock k))
    ((graded_wf (agree_revLex _).irrefl revLexLT_trans).prod_lex
      (graded_wf (agree_revLex _).irrefl revLexLT_trans))

/-- Each strict order is compatible with the product of monomials and cancellative. -/
theorem lt_product : ∀ (o : OrderKind n) (a b c : Exponents n),
    o.Lt a b ↔ o.Lt (a.product c) (b.product c)
  | .lex, _, _, _ => lexLT_product
  | .grlex, _, _, _ => graded_product lexLT_product
  | .grevlex, _, _, _ => grevLexLT_product
  | .block k, a, b, c => by
    simp only [OrderKind.Lt, BlockLT, Prod.lex_def, firstBlock_product, secondBlock_product,
      ← grevLexLT_product, product_right_cancel]

/-- No vector is below the constant one. -/
theorem not_lt_constant : ∀ (o : OrderKind n) (a : Exponents n), ¬o.Lt a Exponents.constant
  | .lex, _ => fun ⟨_, _, h⟩ => Nat.not_lt_zero _ h
  | .grlex, a => graded_not_lt_constant (agree_lex n).irrefl a
  | .grevlex, a => graded_not_lt_constant (agree_revLex n).irrefl a
  | .block _, _ => fun h => by
    rcases Prod.lex_def.mp h with h | ⟨_, h⟩
    exacts [graded_not_lt_constant (agree_revLex _).irrefl _ h,
      graded_not_lt_constant (agree_revLex _).irrefl _ h]

/-- Every vector but the constant one is above it. -/
theorem constant_lt (o : OrderKind n) {a : Exponents n} (h : a ≠ Exponents.constant) :
    o.Lt Exponents.constant a :=
  ((agree o).trichotomous _ a).resolve_right (not_or.mpr ⟨Ne.symm h, not_lt_constant o a⟩)

/-- A vector below another at every variable is below it in each order. -/
theorem lt_of_pointwise (o : OrderKind n) {a b : Exponents n} (h : ∀ i, a i ≤ b i)
    (hne : a ≠ b) : o.Lt a b := by
  have hd : (fun i => b i - a i) ≠ Exponents.constant := fun hd => hne (funext fun i =>
    Nat.le_antisymm (h i) (Nat.sub_eq_zero_iff_le.mp (congrFun hd i)))
  have := (lt_product o _ _ a).mp (constant_lt o hd)
  rwa [show Exponents.constant.product a = a from funext fun i => Nat.zero_add _,
    show Exponents.product (fun i => b i - a i) a = b from
      funext fun i => Nat.sub_add_cancel (h i)] at this

/-! ## Monomial orders of Mathlib -/

/-- The exponent vectors ordered by `o`. -/
def Syn (_ : OrderKind n) : Type := Exponents n

instance (o : OrderKind n) : AddCommMonoid (Syn o) := inferInstanceAs (AddCommMonoid (Exponents n))

instance (o : OrderKind n) : IsStrictTotalOrder (Syn o) o.Lt where
  irrefl := (agree o).irrefl
  trans _ _ _ := orderTrans o
  trichotomous a b h₁ h₂ := (((agree o).trichotomous a b).resolve_left h₁).resolve_right h₂

noncomputable instance (o : OrderKind n) : LinearOrder (Syn o) :=
  @linearOrderOfSTO (Syn o) o.Lt _ (Classical.decRel _)

/-- The order of `Syn o` is equality or the strict order of `o`. -/
theorem syn_le_iff {o : OrderKind n} {a b : Syn o} : a ≤ b ↔ a = b ∨ o.Lt a b := Iff.rfl

instance (o : OrderKind n) : IsOrderedAddMonoid (Syn o) where
  add_le_add_left a b h c := by
    rcases syn_le_iff.mp h with rfl | h
    · exact le_rfl
    · exact syn_le_iff.mpr (.inr ((lt_product o a b c).mp h))

instance (o : OrderKind n) : WellFoundedLT (Syn o) := orderWf o

/-- The monomial order of Mathlib whose strict order is that of `o`. -/
noncomputable def toMathlib (o : OrderKind n) : MonomialOrder.{0, 0} (Fin n) where
  syn := Syn o
  toSyn := { Finsupp.equivFunOnFinite with map_add' := fun _ _ => rfl }
  toSyn_monotone a b h := by
    by_cases hab : a = b
    · exact hab ▸ le_rfl
    · exact syn_le_iff.mpr
        (.inr (lt_of_pointwise o (fun i => h i) fun e => hab (Finsupp.ext (congrFun e))))

/-- `toMathlib o` orders the vectors of Mathlib as `o` orders the exponent vectors. -/
theorem agrees (o : OrderKind n) : o.Agrees (toMathlib o) := fun _ _ => Iff.rfl

/-! ## Block orders as `grevlex` -/

/-- Renumbering the variables by a cast does not change `compareGrevLex`. -/
theorem compareGrevLex_cast {m : ℕ} (h : m = n) (f : Fin m → Fin n) (hf : ∀ j, (f j).val = j.val)
    (a b : Exponents n) :
    compareGrevLex (fun j => a (f j)) (fun j => b (f j)) = compareGrevLex a b := by
  subst h
  obtain rfl : f = id := funext fun j => Fin.ext (hf j)
  rfl

/-- The block order of the split 0 compares as `grevlex`. -/
theorem block_zero (n : ℕ) :
    (OrderKind.block 0 : OrderKind n).compare = OrderKind.grevlex.compare := by
  funext a b
  have h : a.firstBlock 0 = b.firstBlock 0 := funext fun i => absurd i.isLt (by simp)
  simp only [OrderKind.compare, compareBlock, (agree_grevlex _ _).2.1.mpr h, Ordering.eq_then]
  exact compareGrevLex_cast (by simp) _ (fun _ => Nat.zero_add _) a b

/-- The block order of the split `n` compares as `grevlex`. -/
theorem block_last (n : ℕ) :
    (OrderKind.block (Fin.last n) : OrderKind n).compare = OrderKind.grevlex.compare := by
  funext a b
  have h : a.secondBlock (Fin.last n) = b.secondBlock (Fin.last n) :=
    funext fun j => absurd j.isLt (by simp)
  simp only [OrderKind.compare, compareBlock, (agree_grevlex _ _).2.1.mpr h, Ordering.then_eq]
  exact compareGrevLex_cast (by simp) _ (fun j => by simp) a b

/-- A block order puts a vector using its first block above every vector not using it. -/
theorem block_eliminates (k : Fin (n + 1)) {a b : Exponents n}
    (ha : ∃ i : Fin n, i.val < k.val ∧ a i ≠ 0) (hb : ∀ i : Fin n, i.val < k.val → b i = 0) :
    (OrderKind.block k).Lt b a := by
  obtain ⟨i, hi, hai⟩ := ha
  have h₁ : b.firstBlock k = Exponents.constant := funext fun j => hb _ j.isLt
  have h₂ : a.firstBlock k ≠ Exponents.constant := fun h => hai (congrFun h ⟨i, hi⟩)
  refine Prod.lex_def.mpr (.inl ?_)
  show GrevLexLT (b.firstBlock k) (a.firstBlock k)
  rw [h₁]
  exact constant_lt .grevlex h₂

end Orders

open Orders

/-- Proves `MonomialOrdersAreStrictTotalOrders`: irreflexivity and trichotomy from the agreement
of the comparison, and transitivity order by order. -/
public theorem monomialOrdersAreStrictTotalOrders : MonomialOrdersAreStrictTotalOrders :=
  fun _ o => ⟨(agree o).irrefl, fun _ _ _ => orderTrans o, (agree o).trichotomous, agree o⟩

/-- Proves `MonomialOrdersRespectProducts`, order by order. -/
public theorem monomialOrdersRespectProducts : MonomialOrdersRespectProducts :=
  ⟨fun _ _ _ => Finsupp.ext fun _ => rfl, fun _ => lt_product⟩

/-- Proves `MonomialOrdersAreWellFounded`, order by order. -/
public theorem monomialOrdersAreWellFounded : MonomialOrdersAreWellFounded :=
  fun _ => orderWf

/-- Proves `TheConstantMonomialIsLeast`: no vector is below the constant one, and by trichotomy
every other vector is above it. -/
public theorem theConstantMonomialIsLeast : TheConstantMonomialIsLeast :=
  fun _ o => ⟨not_lt_constant o, fun _ => constant_lt o⟩

/-- Proves `BlockOrdersEliminateTheirFirstBlock`. -/
public theorem blockOrdersEliminateTheirFirstBlock : BlockOrdersEliminateTheirFirstBlock :=
  ⟨fun _ k _ _ => ⟨Prod.lex_def, block_eliminates k⟩, fun n => ⟨block_zero n, block_last n⟩⟩

/-- Proves `MonomialOrdersAreThoseOfMathlib` with the monomial order `toMathlib o` on the
exponent vectors ordered by `o`. -/
public theorem monomialOrdersAreThoseOfMathlib : MonomialOrdersAreThoseOfMathlib :=
  fun _ o => ⟨toMathlib o, agrees o, fun a b => (agrees o a b).trans (agree o a b).1.symm⟩

end Kalyx.Proofs.Multivariate
