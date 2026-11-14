module

public import Kalyx.Statements.Terms
public import Kalyx.Proofs.Terms.Sorting

/-!
# Results, nodes and the bases of negative powers

The lemmas about results, nodes and the bases of negative powers that the
proofs of the canonical forms and of their meaning share: `Result` as a
lawful monad; induction over terms; nodes, the nodes of canonical terms,
sizes and `N(t)` read through the nodes; the merge condition of powers; calls
and roots; merging adjacent elements; sorted lists of terms and the maximal
bases, mostly in any order, and the uncovered bases; the contents of sums and
scaled monomials; the nodes of a result that come from its operands
(`NodesFrom`); and the terms that the parts of a product stand for
(`partsTerms`).
-/

namespace Kalyx.Proofs.Terms

open Kalyx.Spec.Terms Kalyx.Statements.Terms

variable {α β : Type}

/-! ## Results -/

/-- `Result` is a lawful monad. -/
public instance instLawfulMonadResult : LawfulMonad Result := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x _ _ => by cases x <;> rfl)
  (seqLeft_eq := fun x y => by cases x <;> cases y <;> rfl)
  (seqRight_eq := fun x y => by cases x <;> cases y <;> rfl)
  (bind_pure_comp := fun _ x => by cases x <;> rfl)
  (bind_map := fun f x => by cases f <;> cases x <;> rfl)

/-- A value is passed on by `bind`. -/
@[simp] public theorem bind_value (v : α) (f : α → Result β) : (Result.value v >>= f) = f v := rfl
/-- A limit stops `bind`. -/
@[simp] public theorem bind_limit (l : Kalyx.Spec.Fields.LimitField) (f : α → Result β) :
    (Result.resourceLimit l >>= f) = .resourceLimit l := rfl
/-- A fault stops `bind`. -/
@[simp] public theorem bind_fault (e : TermFault) (f : α → Result β) :
    (Result.fault e >>= f) = .fault e := rfl
/-- `pure` is a value. -/
@[simp] public theorem pure_value (v : α) : (pure v : Result α) = .value v := rfl
/-- `map` of a value. -/
@[simp] public theorem map_value (f : α → β) (v : α) : (f <$> Result.value v) = .value (f v) := rfl
/-- `map` keeps a limit. -/
@[simp] public theorem map_limit (f : α → β) (l : Kalyx.Spec.Fields.LimitField) :
    (f <$> (Result.resourceLimit l : Result α)) = .resourceLimit l := rfl
/-- `map` keeps a fault. -/
@[simp] public theorem map_fault (f : α → β) (e : TermFault) :
    (f <$> (Result.fault e : Result α)) = .fault e := rfl

/-- A `bind` that returns a value: the first result is a value. -/
public theorem bind_eq_value {x : Result α} {f : α → Result β} {v : β} :
    x >>= f = .value v ↔ ∃ a, x = .value a ∧ f a = .value v := by cases x <;> simp
/-- A `Result.map` that returns a value: the result is a value. -/
public theorem map_eq_value {x : Result α} {f : α → β} {v : β} :
    Result.map f x = .value v ↔ ∃ a, x = .value a ∧ f a = v := by cases x <;> simp [Result.map]

/-- A `mapM` that returns a value returns, for each element, its value under `f`. -/
public theorem mapM_value {f : α → Result β} : ∀ {l : List α} {rs : List β},
    l.mapM f = .value rs → List.Forall₂ (fun a r => f a = .value r) l rs
  | [], rs, h => by simp at h; subst h; exact .nil
  | a :: l, rs, h => by
    rw [List.mapM_cons] at h
    cases hfa : f a <;> rw [hfa] at h <;> try simp at h
    cases hl : l.mapM f <;> rw [hl] at h <;> simp at h
    subst h; exact .cons hfa (mapM_value hl)

/-- The elements of a `mapM` that returns a value, and the values. -/
public theorem mapM_mem {f : α → Result β} {l : List α} {rs : List β} (h : l.mapM f = .value rs) :
    (∀ a ∈ l, ∃ r ∈ rs, f a = .value r) ∧ ∀ r ∈ rs, ∃ a ∈ l, f a = .value r := by
  have h2 := mapM_value h; clear h
  induction h2 with
  | nil => simp
  | cons hab _ ih =>
    simp only [List.mem_cons, forall_eq_or_imp, exists_eq_or_imp]
    exact ⟨⟨.inl hab, fun a ha => let ⟨r, hr, h⟩ := ih.1 a ha; .inr ⟨r, hr, h⟩⟩,
      ⟨.inl hab, fun r hr => let ⟨a, ha, h⟩ := ih.2 r hr; .inr ⟨a, ha, h⟩⟩⟩

/-! ## Induction over terms, nodes and sizes -/

/-- Induction over terms, with a hypothesis for each child in a list of children. -/
public theorem term_induct {P : Term → Prop}
    (number : ∀ q, P (.number q)) (constant : ∀ c, P (.constant c))
    (symbol : ∀ s, P (.symbol s)) (call : ∀ h args, (∀ a ∈ args, P a) → P (.call h args))
    (power : ∀ b k, P b → P (.power b k)) (product : ∀ c fs, (∀ f ∈ fs, P f) → P (.product c fs))
    (sum : ∀ c ms, (∀ m ∈ ms, P m.2) → P (.sum c ms))
    (condition : ∀ s ops, (∀ a ∈ ops, P a) → P (.condition s ops)) : ∀ t, P t := fun t =>
  Term.rec (motive_1 := P) (motive_2 := fun ts => ∀ a ∈ ts, P a)
    (motive_3 := fun ms => ∀ m ∈ ms, P m.2) (motive_4 := fun m => P m.2)
    number constant symbol call power product sum condition
    (by simp) (fun _ _ h1 h2 => List.forall_mem_cons.2 ⟨h1, h2⟩)
    (by simp) (fun _ _ h1 h2 => List.forall_mem_cons.2 ⟨h1, h2⟩) (fun _ _ h => h) t

/-- The nodes of a list are the nodes of its terms. -/
public theorem mem_nodesList {x : Term} :
    ∀ {ts : List Term}, x ∈ Term.nodesList ts ↔ ∃ t ∈ ts, x ∈ t.nodes
  | [] => by simp [Term.nodesList]
  | t :: ts => by simp [Term.nodesList, mem_nodesList]
/-- The nodes of monomials are the nodes of their cores. -/
public theorem mem_nodesPairs {x : Term} :
    ∀ {ms : List (ℚ × Term)}, x ∈ Term.nodesPairs ms ↔ ∃ m ∈ ms, x ∈ m.2.nodes
  | [] => by simp [Term.nodesPairs]
  | (a, t) :: ms => by simp [Term.nodesPairs, mem_nodesPairs]
/-- A term is one of its nodes. -/
public theorem mem_nodes_self (t : Term) : t ∈ t.nodes := by cases t <;> simp [Term.nodes]

/-- A node of a node of `t` is a node of `t`. -/
public theorem nodes_trans {t s x : Term} (hs : s ∈ t.nodes) (hx : x ∈ s.nodes) :
    x ∈ t.nodes := by
  induction t using term_induct generalizing s with
  | number | constant | symbol => rw [Term.nodes, List.mem_singleton] at hs; subst hs; exact hx
  | power b k ih =>
    rw [Term.nodes, List.mem_cons] at hs
    rcases hs with rfl | hs; exacts [hx, by rw [Term.nodes]; exact .tail _ (ih hs hx)]
  | call _ args ih | product _ args ih | condition _ args ih =>
    rw [Term.nodes, List.mem_cons, mem_nodesList] at hs
    rcases hs with rfl | ⟨a, ha, hs⟩
    exacts [hx, by rw [Term.nodes]; exact .tail _ (mem_nodesList.2 ⟨a, ha, ih a ha hs hx⟩)]
  | sum _ ms ih =>
    rw [Term.nodes, List.mem_cons, mem_nodesPairs] at hs
    rcases hs with rfl | ⟨m, hm, hs⟩
    exacts [hx, by rw [Term.nodes]; exact .tail _ (mem_nodesPairs.2 ⟨m, hm, ih m hm hs hx⟩)]

/-- A factor of a product is one of its nodes. -/
public theorem mem_nodes_factor {c : ℚ} {fs : List Term} {f : Term} (hf : f ∈ fs) :
    f ∈ (Term.product c fs).nodes := by
  rw [Term.nodes]; exact .tail _ (mem_nodesList.2 ⟨f, hf, mem_nodes_self f⟩)

/-- The factors of a core are its nodes. -/
public theorem coreFactors_nodes {t f : Term} (h : f ∈ t.coreFactors) : f ∈ t.nodes := by
  cases t <;> simp only [Term.coreFactors, List.mem_singleton] at h <;>
    first | (subst h; exact mem_nodes_self _) | exact .tail _ (mem_nodesList.2 ⟨f, h, mem_nodes_self f⟩)

/-- A number is canonical. -/
public theorem canonical_number {o : Orders} {me : ℕ} {R : RegistryRules} (q : ℚ) :
    Term.Canonical o me R (.number q) :=
  ⟨by simp [Term.shapeOk, Term.nodes, Term.nodeOk], fun c hc => by simp [Term.nodes] at hc⟩

/-- A node of a canonical term is canonical. -/
public theorem canonical_node {o : Orders} {me : ℕ} {R : RegistryRules} {t x : Term}
    (ht : Term.Canonical o me R t) (hx : x ∈ t.nodes) : Term.Canonical o me R x :=
  ⟨List.all_eq_true.2 fun y hy => List.all_eq_true.1 ht.1 y (nodes_trans hx hy),
    fun c hc => ht.2 c (nodes_trans hx hc)⟩

/-- A term of a list is no larger than the list. -/
private theorem size_le_sizeList {t : Term} :
    ∀ {ts : List Term}, t ∈ ts → t.size ≤ Term.sizeList ts
  | _ :: _, .head _ => Nat.le_add_right _ _
  | _ :: _, .tail _ h => (size_le_sizeList h).trans (Nat.le_add_left _ _)
/-- A core of monomials is no larger than the monomials. -/
private theorem size_le_sizePairs {m : ℚ × Term} :
    ∀ {ms : List (ℚ × Term)}, m ∈ ms → m.2.size ≤ Term.sizePairs ms
  | (_, _) :: _, .head _ => Nat.le_add_right _ _
  | (_, _) :: _, .tail _ h => (size_le_sizePairs h).trans (Nat.le_add_left _ _)

/-- A node is no larger than the term. -/
public theorem size_le {t x : Term} (h : x ∈ t.nodes) : x.size ≤ t.size := by
  induction t using term_induct with
  | number | constant | symbol => rw [Term.nodes, List.mem_singleton] at h; subst h; exact le_rfl
  | power b k ih =>
    rw [Term.nodes, List.mem_cons] at h
    rcases h with rfl | h; exacts [le_rfl, by have := ih h; simp only [Term.size]; omega]
  | call _ args ih | product _ args ih | condition _ args ih =>
    rw [Term.nodes, List.mem_cons, mem_nodesList] at h
    rcases h with rfl | ⟨a, ha, h⟩; · exact le_rfl
    have := ih a ha h; have := size_le_sizeList ha; simp only [Term.size]; omega
  | sum _ ms ih =>
    rw [Term.nodes, List.mem_cons, mem_nodesPairs] at h
    rcases h with rfl | ⟨m, hm, h⟩; · exact le_rfl
    have := ih m hm h; have := size_le_sizePairs hm; simp only [Term.size]; omega

/-! ## The bases of negative powers -/

/-- `N` of a list holds `N` of each of its terms. -/
public theorem mem_negBasesList {b : Term} :
    ∀ {ts : List Term}, b ∈ Term.negBasesList ts ↔ ∃ t ∈ ts, b ∈ t.negBases
  | [] => by simp [Term.negBasesList]
  | t :: ts => by simp [Term.negBasesList, mem_negBasesList]
/-- `N` of monomials holds `N` of each of their cores. -/
public theorem mem_negBasesPairs {b : Term} :
    ∀ {ms : List (ℚ × Term)}, b ∈ Term.negBasesPairs ms ↔ ∃ m ∈ ms, b ∈ m.2.negBases
  | [] => by simp [Term.negBasesPairs]
  | (_, t) :: ms => by simp [Term.negBasesPairs, mem_negBasesPairs]

/-- `N(t)`: the bases, not constants, of the powers with negative exponents among the nodes. -/
public theorem mem_negBases {t b : Term} :
    b ∈ t.negBases ↔ ∃ k < 0, b.isConstant = false ∧ Term.power b k ∈ t.nodes := by
  induction t using term_induct with
  | number | constant | symbol => simp [Term.negBases, Term.nodes]
  | power c j ih =>
    simp only [Term.negBases, Term.nodes, List.mem_append, List.mem_cons, Term.power.injEq, ih,
      List.mem_ite_nil_right, List.not_mem_nil, or_false, Bool.not_eq_true']
    constructor
    · rintro (⟨⟨hj, hc⟩, rfl⟩ | ⟨k, hk, hc, hn⟩)
      exacts [⟨j, hj, hc, .inl ⟨rfl, rfl⟩⟩, ⟨k, hk, hc, .inr hn⟩]
    · rintro ⟨k, hk, hc, ⟨rfl, rfl⟩ | hn⟩
      exacts [.inl ⟨⟨hk, hc⟩, rfl⟩, .inr ⟨k, hk, hc, hn⟩]
  | call _ args ih | product _ args ih | condition _ args ih =>
    simp only [Term.negBases, Term.nodes, List.mem_cons, reduceCtorEq, false_or,
      mem_negBasesList, mem_nodesList]
    exact ⟨fun ⟨a, ha, hb⟩ => let ⟨k, hk, hc, hn⟩ := (ih a ha).1 hb; ⟨k, hk, hc, a, ha, hn⟩,
      fun ⟨k, hk, hc, a, ha, hn⟩ => ⟨a, ha, (ih a ha).2 ⟨k, hk, hc, hn⟩⟩⟩
  | sum _ ms ih =>
    simp only [Term.negBases, Term.nodes, List.mem_cons, reduceCtorEq, false_or,
      mem_negBasesPairs, mem_nodesPairs]
    exact ⟨fun ⟨m, hm, hb⟩ => let ⟨k, hk, hc, hn⟩ := (ih m hm).1 hb; ⟨k, hk, hc, m, hm, hn⟩,
      fun ⟨k, hk, hc, m, hm, hn⟩ => ⟨m, hm, (ih m hm).2 ⟨k, hk, hc, hn⟩⟩⟩

/-- A base of `N` is not a constant. -/
public theorem negBases_isConstant {t b : Term} (h : b ∈ t.negBases) : b.isConstant = false :=
  let ⟨_, _, hc, _⟩ := mem_negBases.1 h; hc
/-- A base of `N` is a node. -/
public theorem negBases_mem_nodes {t b : Term} (h : b ∈ t.negBases) : b ∈ t.nodes :=
  let ⟨_, _, _, hn⟩ := mem_negBases.1 h
  nodes_trans hn (by rw [Term.nodes]; exact .tail _ (mem_nodes_self b))
/-- A base of `N` is smaller than the term. -/
public theorem negBases_size {t b : Term} (h : b ∈ t.negBases) : b.size < t.size := by
  obtain ⟨k, -, -, hn⟩ := mem_negBases.1 h
  have := size_le hn; simp only [Term.size] at this; omega
/-- `N` is transitive. -/
public theorem negBases_trans {t b c : Term} (hb : b ∈ t.negBases) (hc : c ∈ b.negBases) :
    c ∈ t.negBases :=
  let ⟨k, hk, hk', hn⟩ := mem_negBases.1 hc
  mem_negBases.2 ⟨k, hk, hk', nodes_trans (negBases_mem_nodes hb) hn⟩
/-- `N` of a power with an exponent of at least 0 is that of its base. -/
public theorem negBases_power_pos {b : Term} {k : ℤ} (hk : 0 ≤ k) :
    (Term.power b k).negBases = b.negBases := by simp [Term.negBases, not_lt.2 hk]

/-! ## The merge condition of powers -/

/-- The merge condition holds exactly for a nonnegative inner or a positive outer exponent. -/
public theorem mergeCondition_iff {j k : ℤ} : mergeCondition j k = true ↔ 0 ≤ j ∨ 0 < k := by
  have h1 : j < 0 → 0 < k → j * k < 0 := mul_neg_of_neg_of_pos
  have h2 : 0 < j → k < 0 → j * k < 0 := mul_neg_of_pos_of_neg
  have h3 : j < 0 → k ≤ 0 → 0 ≤ j * k := fun a b => mul_nonneg_of_nonpos_of_nonpos a.le b
  simp only [mergeCondition, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  omega

/-- The merge condition fails exactly for a negative inner and a nonpositive outer exponent. -/
public theorem mergeCondition_false {j k : ℤ} : mergeCondition j k = false ↔ j < 0 ∧ k ≤ 0 := by
  rw [← Bool.not_eq_true, mergeCondition_iff]; omega

/-! ## Calls and roots -/

/-- A root has a degree of at least 2, its radicand first and numbers as its other arguments. -/
public theorem rootOf_some {b u : Term} {n : ℕ} (h : rootOf b = some (u, n)) :
    2 ≤ n ∧ ∃ hd rest, b = .call hd (u :: rest) ∧ ∀ a ∈ rest, ∃ q, a = .number q := by
  unfold rootOf at h
  split at h <;> (try split at h) <;> simp only [Option.some.injEq, Prod.mk.injEq,
    reduceCtorEq] at h <;> obtain ⟨rfl, rfl⟩ := h
  · exact ⟨le_rfl, _, _, rfl, by simp⟩
  · rename_i q hq
    refine ⟨?_, _, _, rfl, by simp⟩
    have : (1 : ℤ) < q.num := by
      rw [← Rat.coe_int_num_of_den_eq_one hq.2.1] at hq; exact_mod_cast hq.2.2
    omega

/-- A factor is a value. -/
public theorem factorOk_value {b : Term} (h : b.factorOk = true) : b.isCondition = false := by
  cases b <;> simp_all [Term.factorOk, Term.isCondition]
/-- A core is a value. -/
public theorem coreOk_value {b : Term} (h : b.coreOk = true) : b.isCondition = false := by
  cases b <;> simp_all [Term.coreOk, Term.isCondition]

/-- Only `piecewise` takes a condition, at its first position. -/
public theorem role_condition {h : Head} {i : ℕ} (hr : h.role i = .condition) :
    h = Head.piecewise := by
  rcases h with ⟨name, cls⟩; unfold Head.role at hr; split at hr
  · rename_i h1 h2; simp only at h1 h2; subst h1 h2; rfl
  all_goals cases hr

/-- The arguments of a call other than `piecewise` that `argsOkFrom` accepts are values. -/
public theorem argsOkFrom_values {h : Head} (hp : h ≠ Head.piecewise) :
    ∀ {i : ℕ} {args : List Term}, h.argsOkFrom i args = true → ∀ a ∈ args, a.isCondition = false
  | _, [], _ => by simp
  | i, t :: ts, hok => by
    simp only [Head.argsOkFrom, Bool.and_eq_true, beq_iff_eq] at hok
    refine List.forall_mem_cons.2 ⟨?_, argsOkFrom_values hp hok.2⟩
    rw [hok.1, beq_eq_false_iff_ne.2 fun e => hp (role_condition e)]

/-- The radicand of a root of a canonical term is a canonical value. -/
public theorem root_radicand {o : Orders} {me : ℕ} {R : RegistryRules} {b u : Term} {n : ℕ}
    (hb : Term.Canonical o me R b) (h : rootOf b = some (u, n)) :
    Term.Canonical o me R u ∧ u.isCondition = false := by
  obtain ⟨-, hd, rest, rfl, -⟩ := rootOf_some h
  have hok := List.all_eq_true.1 hb.1 _ (mem_nodes_self _)
  simp only [Term.nodeOk, canonicalCall, Bool.and_eq_true] at hok
  refine ⟨canonical_node hb (by simp [Term.nodes, Term.nodesList, mem_nodes_self]),
    argsOkFrom_values (fun e => ?_) hok.1.1 u (by simp)⟩
  subst e; unfold rootOf at h; split at h <;> (try split at h) <;> simp_all [Head.piecewise]

/-! ## Merging adjacent elements -/

/-- The first element stays before the merged rest, or joins its first element. -/
public theorem mergeAdjacent_cons (join : α → α → Option α) (x : α) (rest : List α) :
    mergeAdjacent join (x :: rest) = x :: mergeAdjacent join rest ∨
      ∃ y more z, mergeAdjacent join rest = y :: more ∧ join x y = some z ∧
        mergeAdjacent join (x :: rest) = z :: more := by
  rcases hm : mergeAdjacent join rest with _ | ⟨y, more⟩
  · simp [mergeAdjacent, hm]
  · cases hz : join x y <;> simp [mergeAdjacent, hm, hz]

/-- Merging keeps a property that each join keeps. -/
public theorem mergeAdjacent_forall (join : α → α → Option α) (P : α → Prop)
    (hj : ∀ x y z, join x y = some z → P x → P y → P z) :
    ∀ (l : List α), (∀ a ∈ l, P a) → ∀ z ∈ mergeAdjacent join l, P z
  | [], _ => by simp [mergeAdjacent]
  | x :: rest, h => by
    have ih := mergeAdjacent_forall join P hj rest fun a ha => h a (.tail _ ha)
    rcases mergeAdjacent_cons join x rest with e | ⟨y, more, z, hm, hz, e⟩ <;> rw [e] <;>
      (try rw [hm] at ih) <;> intro w hw <;> rcases List.mem_cons.1 hw with rfl | hw
    exacts [h w (by simp), ih w hw, hj x y w hz (h x (by simp)) (ih y (by simp)), ih w (.tail _ hw)]

/-- Every merged element has an element of the same image under `g`, when the
joins keep `g`. -/
public theorem mergeAdjacent_from (join : α → α → Option α) (g : α → β)
    (hj : ∀ x y z, join x y = some z → g x = g z ∧ g y = g z) (l : List α) :
    ∀ z ∈ mergeAdjacent join l, ∃ a ∈ l, g a = g z :=
  mergeAdjacent_forall join (fun z => ∃ a ∈ l, g a = g z)
    (fun _ _ _ hz ⟨a, ha, e⟩ _ => ⟨a, ha, e.trans (hj _ _ _ hz).1⟩) l fun a ha => ⟨a, ha, rfl⟩

/-- Every element has a merged element of the same image under `g`, when the
joins keep `g`. -/
public theorem mergeAdjacent_cover (join : α → α → Option α) (g : α → β)
    (hj : ∀ x y z, join x y = some z → g x = g z ∧ g y = g z) :
    ∀ (l : List α), ∀ a ∈ l, ∃ z ∈ mergeAdjacent join l, g z = g a
  | [] => by simp
  | x :: rest => by
    intro a ha
    have ih := mergeAdjacent_cover join g hj rest
    rcases mergeAdjacent_cons join x rest with e | ⟨y, more, z, hm, hz, e⟩ <;> rw [e] <;>
      rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨a, by simp, rfl⟩
    · obtain ⟨w, hw, hg⟩ := ih a ha; exact ⟨w, .tail _ hw, hg⟩
    · exact ⟨z, by simp, (hj _ _ _ hz).1.symm⟩
    obtain ⟨w, hw, hg⟩ := ih a ha
    rcases List.mem_cons.1 (hm ▸ hw) with rfl | hw
    exacts [⟨z, by simp, (hj _ _ _ hz).2.symm.trans hg⟩, ⟨w, .tail _ hw, hg⟩]

/-- Merging keeps a sum of weights that each join keeps. -/
public theorem mergeAdjacent_sum {M : Type} [AddCommMonoid M] (join : α → α → Option α)
    (f : α → M) (hj : ∀ x y z, join x y = some z → f z = f x + f y) :
    ∀ l : List α, ((mergeAdjacent join l).map f).sum = (l.map f).sum
  | [] => by simp [mergeAdjacent]
  | x :: rest => by
    have ih := mergeAdjacent_sum join f hj rest
    rcases mergeAdjacent_cons join x rest with e | ⟨y, more, z, hm, hz, e⟩ <;> rw [e]
    · simp [ih]
    · rw [hm] at ih; simp only [List.map_cons, List.sum_cons] at ih ⊢
      rw [hj x y z hz, add_assoc, ih]

/-! ## Sorted lists of terms and maximal bases -/

/-- A sorted list of terms has the terms of the list, in any order of terms. -/
public theorem mem_sortedTerms' {o : Orders} {ts : List Term} {t : Term} :
    t ∈ sortedTerms o ts ↔ t ∈ ts := by
  have hj : ∀ a b z : Term, (if a = b then some a else none) = some z →
      id a = id z ∧ id b = id z := fun a b z h => by split at h <;> simp_all
  rw [← (perm_sortBy (Term.cmp o) ts).mem_iff, sortedTerms]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := mergeAdjacent_from _ id hj _ t h; exact ha
  · obtain ⟨z, hz, rfl⟩ := mergeAdjacent_cover _ id hj _ t h; exact hz

/-- The maximal elements, in any order of terms: the bases negative inside none of them. -/
public theorem mem_maxBases' {o : Orders} {bs : List Term} {b : Term} :
    b ∈ maxBases o bs ↔ b ∈ bs ∧ ∀ c ∈ bs, b ∉ c.negBases := by
  simp [maxBases, mem_sortedTerms']

/-- The maximal elements depend only on the elements of the list of bases. -/
public theorem maxBases_congr {o : Orders} (hc : TotalCmp (Term.cmp o)) {bs bs' : List Term}
    (h : ∀ t, t ∈ bs ↔ t ∈ bs') : maxBases o bs = maxBases o bs' :=
  eq_of_strictlyIncreasing hc (maxBases_strictlyIncreasing hc bs)
    (maxBases_strictlyIncreasing hc bs') fun t => by simp only [mem_maxBases', h]

/-- A maximal element is an element. -/
public theorem maxBases_subset {o : Orders} {bs : List Term} {b : Term}
    (h : b ∈ maxBases o bs) : b ∈ bs := (mem_maxBases'.1 h).1

/-- Every base of a list is maximal or in `N` of a maximal one. -/
public theorem maxBases_cover (o : Orders) (bs : List Term) {x : Term} (hx : x ∈ bs) :
    x ∈ maxBases o bs ∨ ∃ m ∈ maxBases o bs, x ∈ m.negBases := by
  induction hn : (bs.map Term.size).sum - x.size using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    by_cases hmax : ∀ c ∈ bs, x ∉ c.negBases
    · exact .inl (mem_maxBases'.2 ⟨hx, hmax⟩)
    push Not at hmax
    obtain ⟨c, hc, hxc⟩ := hmax
    have := negBases_size hxc; have := List.le_sum_of_mem (List.mem_map_of_mem (f := Term.size) hc)
    rcases ih _ (by omega) hc rfl with h | ⟨m, hm, hcm⟩
    exacts [.inr ⟨c, h, hxc⟩, .inr ⟨m, hm, negBases_trans hcm hxc⟩]

/-- The maximal elements are empty only for no bases. -/
public theorem maxBases_eq_nil {o : Orders} {bs : List Term} : maxBases o bs = [] ↔ bs = [] := by
  refine ⟨fun h => List.eq_nil_iff_forall_not_mem.2 fun x hx => ?_, fun h => by subst h; rfl⟩
  rcases maxBases_cover o bs hx with h' | ⟨m, h', -⟩ <;> simp [h] at h'

/-- `N` of the reciprocals of bases that are not constants: the bases and their `N`. -/
public theorem mem_negBases_reciprocals {bs : List Term} (hbs : ∀ b ∈ bs, b.isConstant = false)
    {x : Term} :
    x ∈ Term.negBasesList (bs.map Term.reciprocal) ↔ ∃ b ∈ bs, x = b ∨ x ∈ b.negBases := by
  simp only [mem_negBasesList, List.mem_map, exists_exists_and_eq_and]
  refine exists_congr fun b => and_congr_right fun hb => ?_
  simp [Term.reciprocal, Term.negBases, hbs b hb]

/-- The elements of `uncovered`. -/
public theorem mem_uncovered {b : Term} {bs cs : List Term} :
    b ∈ uncovered bs cs ↔ b ∈ bs ∧ b ∉ cs := by
  simp [uncovered]

/-! ## Contents of sums and scaled monomials -/

/-- A content of 0 means the constant 0 and the coefficients 0. -/
public theorem sumContent_eq_zero {c : ℚ} : ∀ {ms : List (ℚ × Term)}, sumContent c ms = 0 →
    c = 0 ∧ ∀ m ∈ ms, m.1 = 0
  | [], h => ⟨h, by simp⟩
  | (a, t) :: ms, h => by
    rw [sumContent] at h
    split at h
    · obtain ⟨h1, h2⟩ := sumContent_eq_zero h
      exact ⟨h1, List.forall_mem_cons.2 ⟨‹a = 0›, h2⟩⟩
    · exact absurd h ‹¬a = 0›

/-- A canonical sum has a content other than 0. -/
public theorem sumContent_ne_zero {o : Orders} {c : ℚ} {ms : List (ℚ × Term)}
    (h : canonicalSum o c ms = true) : sumContent c ms ≠ 0 := by
  intro h0
  obtain ⟨hc, hz⟩ := sumContent_eq_zero h0
  simp only [canonicalSum, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [List.filter_eq_self.2 (by simpa using hz)] at h
  rcases ms with _ | ⟨m, _ | ⟨m', ms⟩⟩ <;> simp_all

/-- The content of a scaled sum. -/
public theorem sumContent_scale {a : ℚ} (ha : a ≠ 0) (c : ℚ) : ∀ ms : List (ℚ × Term),
    sumContent (a * c) (ms.map fun m => (a * m.1, m.2)) = a * sumContent c ms
  | [] => rfl
  | (b, t) :: ms => by
    simp only [List.map_cons, sumContent, mul_eq_zero, ha, false_or, sumContent_scale ha c ms]
    split_ifs <;> rfl

/-- Scaled monomials hold the same bases in `N`. -/
public theorem negBasesPairs_map (a : ℚ) : ∀ ms : List (ℚ × Term),
    Term.negBasesPairs (ms.map fun m => (a * m.1, m.2)) = Term.negBasesPairs ms
  | [] => rfl
  | (_, t) :: ms => by simp only [List.map_cons, Term.negBasesPairs, negBasesPairs_map a ms]

/-! ## Nodes that come from the operands -/

/-- Every node of `u` is a number, a power, a product or a sum, which the
constructors build, or a node of one of the terms `ts`. -/
@[expose] public def NodesFrom (ts : List Term) (u : Term) : Prop :=
  ∀ x ∈ u.nodes, (x.rank = 0 ∨ 4 ≤ x.rank ∧ x.rank ≤ 6) ∨ ∃ t ∈ ts, x ∈ t.nodes

/-- A node of one of `ts` comes from `ts`. -/
public theorem NodesFrom.of_mem {ts : List Term} {t x : Term} (ht : t ∈ ts) (hx : x ∈ t.nodes) :
    NodesFrom ts x := fun _ hy => .inr ⟨t, ht, nodes_trans hx hy⟩
/-- A term of `ts` comes from `ts`. -/
public theorem NodesFrom.self {ts : List Term} {t : Term} (ht : t ∈ ts) : NodesFrom ts t :=
  .of_mem ht (mem_nodes_self t)
/-- The nodes of a term that comes from `ts` come from `ts`. -/
public theorem NodesFrom.sub {ts : List Term} {u x : Term} (hu : NodesFrom ts u)
    (hx : x ∈ u.nodes) : NodesFrom ts x := fun _ hy => hu _ (nodes_trans hx hy)
/-- Coming from `ts` is kept by more terms. -/
public theorem NodesFrom.mono {ts ts' : List Term} {u : Term} (h : ∀ t ∈ ts, t ∈ ts')
    (hu : NodesFrom ts u) : NodesFrom ts' u :=
  fun x hx => (hu x hx).imp_right fun ⟨t, ht, h'⟩ => ⟨t, h t ht, h'⟩
/-- Coming from terms that come from `ts` is coming from `ts`. -/
public theorem NodesFrom.trans' {ss ts : List Term} {u : Term} (hu : NodesFrom ss u)
    (hs : ∀ s ∈ ss, NodesFrom ts s) : NodesFrom ts u :=
  fun x hx => (hu x hx).elim .inl fun ⟨s, hs', hxs⟩ => hs s hs' x hxs

/-- A number comes from any terms. -/
public theorem NodesFrom.number {ts : List Term} (q : ℚ) : NodesFrom ts (.number q) := by
  intro x hx; simp only [Term.nodes, List.mem_singleton] at hx; subst hx; simp [Term.rank]
/-- A power of a base that comes from `ts` comes from `ts`. -/
public theorem NodesFrom.power {ts : List Term} {b : Term} (k : ℤ) (hb : NodesFrom ts b) :
    NodesFrom ts (.power b k) := by
  intro x hx; rw [Term.nodes, List.mem_cons] at hx
  rcases hx with rfl | hx; exacts [.inl (by simp [Term.rank]), hb x hx]
/-- A product of factors that come from `ts` comes from `ts`. -/
public theorem NodesFrom.product {ts fs : List Term} (c : ℚ) (hf : ∀ f ∈ fs, NodesFrom ts f) :
    NodesFrom ts (.product c fs) := by
  intro x hx; rw [Term.nodes, List.mem_cons, mem_nodesList] at hx
  rcases hx with rfl | ⟨f, hf', hx⟩; exacts [.inl (by simp [Term.rank]), hf f hf' x hx]
/-- A sum of monomials whose cores come from `ts` comes from `ts`. -/
public theorem NodesFrom.sum {ts : List Term} {ms : List (ℚ × Term)} (c : ℚ)
    (hm : ∀ m ∈ ms, NodesFrom ts m.2) : NodesFrom ts (.sum c ms) := by
  intro x hx; rw [Term.nodes, List.mem_cons, mem_nodesPairs] at hx
  rcases hx with rfl | ⟨m, hm', hx⟩; exacts [.inl (by simp [Term.rank]), hm m hm' x hx]

/-- Every call of a term whose nodes come from `ts` is a call of one of `ts`. -/
public theorem callsWithin_of_nodesFrom {ts : List Term} {u : Term} (h : NodesFrom ts u) :
    CallsWithin u ts := fun _ _ hc => (h _ hc).resolve_left (by simp [Term.rank])

/-! ## The parts of products -/

/-- The terms that the parts of a product stand for: the power `b ^ k` of each
item `(b, k)`, and the ones. -/
@[expose] public def partsTerms (p : ProductParts) : List Term :=
  p.items.map (fun x => Term.power x.1 x.2) ++ p.ones
/-- A fold of appends of parts. -/
public theorem foldl_append (rs : List ProductParts) : ∀ p : ProductParts,
    rs.foldl ProductParts.append p =
      ⟨p.coefficient * (rs.map (·.coefficient)).prod, p.items ++ (rs.map (·.items)).flatten,
        p.ones ++ (rs.map (·.ones)).flatten⟩ := by
  induction rs with
  | nil => intro p; simp
  | cons r rs ih => intro p; simp [ih, ProductParts.append, mul_assoc]

/-- The terms of the parts of two products together. -/
public theorem mem_partsTerms_append {p q : ProductParts} {s : Term} :
    s ∈ partsTerms (p.append q) ↔ s ∈ partsTerms p ∨ s ∈ partsTerms q := by
  simp only [partsTerms, ProductParts.append, List.map_append, List.mem_append]; tauto
/-- The terms of a fold of parts. -/
public theorem mem_partsTerms_foldl {s : Term} (ps : List ProductParts) : ∀ p : ProductParts,
    s ∈ partsTerms (ps.foldl ProductParts.append p) ↔
      s ∈ partsTerms p ∨ ∃ r ∈ ps, s ∈ partsTerms r := by
  induction ps with
  | nil => simp
  | cons r ps ih =>
    intro p
    simp only [List.foldl_cons, ih, mem_partsTerms_append, List.mem_cons, exists_eq_or_imp]
    tauto
/-- The items of a fold of parts. -/
public theorem mem_items_foldl {x : Term × ℤ} (ps : List ProductParts) : ∀ p : ProductParts,
    x ∈ (ps.foldl ProductParts.append p).items ↔ x ∈ p.items ∨ ∃ r ∈ ps, x ∈ r.items := by
  intro p; rw [foldl_append]; simp

end Kalyx.Proofs.Terms
