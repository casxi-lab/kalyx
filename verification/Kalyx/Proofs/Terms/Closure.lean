module

public import Kalyx.Statements.Terms
public import Kalyx.Proofs.Terms.Basics
public import Kalyx.Proofs.Terms.Sorting
public import Kalyx.Proofs.Terms.Order
public import Kalyx.Proofs.Terms.Sums
public import Kalyx.Proofs.Terms.Products
public import Kalyx.Proofs.Terms.Settle
public import Kalyx.Proofs.Terms.Bases

/-!
# Closure and idempotence of the canonical forms

Proves `CanonicalFormsAreClosedAndIdempotent` and `NegationReadsOpposite`. The canonical form
is read node by node, so each constructor is checked only at the nodes it builds: the witnesses
and the ones over bases of `N` of canonical terms, the cancelled monomials of a sum, the items
of a product through its rounds (a canonical base that is no one, over a power with negative
exponents), the assembly of the settled items with the ones kept, and the merged powers. For
the rebuild, a canonical value is read as a coefficient and canonical factors whose items are
settled: the rounds leave them as they are, the ones kept are the ones of the factors, and the
assembly gives the value back, under a positive limit that allows its exponents. The negation
of a canonical term is that product with the coefficient negated, so it reads back in a sum
with opposite parts.
-/

namespace Kalyx.Proofs.Terms.Closure

open Kalyx.Spec.Terms Kalyx.Statements.Terms Kalyx.Proofs.Terms

variable {α β : Type} {o : Orders} {me : ℕ} {R : RegistryRules}

/-! ## Results -/

/-- A value with `P`, `ResourceLimit`, or a fault other than `Internal`. -/
private def OK (P : α → Prop) : Result α → Prop
  | .value v => P v
  | .fault e => e ≠ .internal
  | .resourceLimit _ => True

/-- `OK` through a `bind`. -/
private theorem OK.bind {P : α → Prop} {Q : β → Prop} {x : Result α} {f : α → Result β}
    (hx : OK P x) (hf : ∀ v, P v → OK Q (f v)) : OK Q (x >>= f) := by
  cases x <;> simp_all [OK]

/-- `OK` of a value. -/
private theorem OK.pure {P : α → Prop} {v : α} (h : P v) : OK P (pure v) := h

/-- `OK` through a check of an exponent. -/
private theorem OK.check {P : α → Prop} {k : ℤ} {n : Unit → Result α} (h : OK P (n ())) :
    OK P (checkExponent me k n) := by
  unfold checkExponent; split; exacts [trivial, h]

/-- `OK` through `mapM`. -/
private theorem OK.mapM {f : α → Result β} {P : β → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, OK P (f a)) → OK (fun rs => ∀ r ∈ rs, P r) (l.mapM f)
  | [], _ => by simp [OK]
  | a :: l, h => by
    rw [List.mapM_cons]
    exact (h a (by simp)).bind fun v hv => (OK.mapM fun x hx => h x (.tail _ hx)).bind
      fun rs hrs => OK.pure (by simpa [hv] using hrs)

/-- A value or `ResourceLimit` with `P` on the value. -/
private theorem OK.of_vl {P : α → Prop} {r : Result α}
    (h : (∃ v, r = .value v) ∨ r = .resourceLimit .exponent) (hv : ∀ v, r = .value v → P v) :
    OK P r := by
  rcases h with ⟨v, rfl⟩ | rfl; exacts [hv v rfl, trivial]

/-- The strict power of a rational is a value or `DivisionByZero`. -/
private theorem ratPow_ok (r : ℚ) (k : ℤ) :
    OK (fun _ => True) (Result.ofOutcome (Kalyx.Spec.Fields.ratPowOp r k)) := by
  unfold Kalyx.Spec.Fields.ratPowOp Kalyx.Spec.Fields.ratPow Kalyx.Spec.Fields.FieldError.lift
  split <;> simp [OK, Result.ofOutcome, TermFault.ofFieldError]

/-! ## The canonical form, node by node -/

/-- What the canonical form asks of one node. -/
private abbrev NodeOk (o : Orders) (me : ℕ) (R : RegistryRules) (x : Term) : Prop :=
  x.nodeOk o me R = true ∧ ∀ c, x = .constant c → c.Valid

/-- The canonical form: every node has its shape and holds a valid constant. -/
private theorem canon_iff {t : Term} :
    Term.Canonical o me R t ↔ ∀ x ∈ t.nodes, NodeOk o me R x := by
  simp only [Term.Canonical, Term.shapeOk, Term.ConstantsValid, List.all_eq_true]
  exact ⟨fun ⟨h1, h2⟩ x hx => ⟨h1 x hx, fun c e => h2 c (e ▸ hx)⟩,
    fun h => ⟨fun x hx => (h x hx).1, fun c hc => (h _ hc).2 c rfl⟩⟩

/-- The nodes of a list of canonical terms. -/
private theorem canon_list {l : List Term} :
    (∀ x ∈ Term.nodesList l, NodeOk o me R x) ↔ ∀ f ∈ l, Term.Canonical o me R f := by
  refine ⟨fun h f hf => canon_iff.2 fun x hx => h x (mem_nodesList.2 ⟨f, hf, hx⟩), fun h x hx => ?_⟩
  obtain ⟨f, hf, hx⟩ := mem_nodesList.1 hx; exact canon_iff.1 (h f hf) x hx

/-- The nodes of monomials with canonical cores. -/
private theorem canon_pairs {ms : List (ℚ × Term)} :
    (∀ x ∈ Term.nodesPairs ms, NodeOk o me R x) ↔ ∀ m ∈ ms, Term.Canonical o me R m.2 := by
  refine ⟨fun h m hm => canon_iff.2 fun x hx => h x (mem_nodesPairs.2 ⟨m, hm, hx⟩),
    fun h x hx => ?_⟩
  obtain ⟨m, hm, hx⟩ := mem_nodesPairs.1 hx; exact canon_iff.1 (h m hm) x hx

/-- A canonical power. -/
private theorem canon_power {b : Term} {k : ℤ} :
    Term.Canonical o me R (.power b k) ↔ canonicalPower b k = true ∧ Term.Canonical o me R b := by
  rw [canon_iff, Term.nodes, List.forall_mem_cons, ← canon_iff]; simp [NodeOk, Term.nodeOk]

/-- A canonical product. -/
private theorem canon_product {c : ℚ} {fs : List Term} : Term.Canonical o me R (.product c fs) ↔
    canonicalProduct o c fs = true ∧ ∀ f ∈ fs, Term.Canonical o me R f := by
  rw [canon_iff, Term.nodes, List.forall_mem_cons, canon_list]; simp [NodeOk, Term.nodeOk]

/-- A canonical sum. -/
private theorem canon_sum {c : ℚ} {ms : List (ℚ × Term)} : Term.Canonical o me R (.sum c ms) ↔
    canonicalSum o c ms = true ∧ ∀ m ∈ ms, Term.Canonical o me R m.2 := by
  rw [canon_iff, Term.nodes, List.forall_mem_cons, canon_pairs]; simp [NodeOk, Term.nodeOk]

/-- A canonical call. -/
private theorem canon_call {h : Head} {args : List Term} : Term.Canonical o me R (.call h args) ↔
    canonicalCall me R h args = true ∧ ∀ a ∈ args, Term.Canonical o me R a := by
  rw [canon_iff, Term.nodes, List.forall_mem_cons, canon_list]; simp [NodeOk, Term.nodeOk]

/-- A canonical condition. -/
private theorem canon_condition {s : CondShape} {ops : List Term} :
    Term.Canonical o me R (.condition s ops) ↔ s.takes ops = true ∧
      ∀ a ∈ ops, Term.Canonical o me R a := by
  rw [canon_iff, Term.nodes, List.forall_mem_cons, canon_list]; simp [NodeOk, Term.nodeOk]

/-- The shape of a power node, condition by condition. -/
private theorem canonicalPower_iff {b : Term} {k : ℤ} : canonicalPower b k = true ↔
    b.factorOk = true ∧ b ≠ Term.imaginaryUnit ∧ k ≠ 1 ∧
      (∀ u n, rootOf b = some (u, n) → k < n) ∧
      (∀ c j, b = .power c j → mergeCondition j k = false ∧
        (k ≠ 0 ∨ (j = -1 ∧ c.isConstant = false))) ∧
      ((∀ c j, b ≠ .power c j) → k ≠ 0) := by
  unfold canonicalPower
  rcases hr : rootOf b with _ | ⟨u, n⟩ <;> cases b <;> simp_all [and_assoc]

/-! ## Witnesses and ones -/

/-- `unnested` by membership. -/
private theorem unnested_iff {bs : List Term} :
    unnested bs = true ↔ ∀ b ∈ bs, ∀ c ∈ bs, b ∉ c.negBases := by
  simp [unnested, List.all_eq_true]

/-- The maximal elements are unnested. -/
private theorem unnested_maxBases (L : List Term) : unnested (maxBases o L) = true :=
  unnested_iff.2 fun _ hb c hc => (mem_maxBases'.1 hb).2 c (maxBases_subset hc)

/-- No base holds itself with a negative exponent. -/
private theorem not_mem_self (b : Term) : b ∉ b.negBases := fun h => lt_irrefl _ (negBases_size h)

/-- Sorted unnested bases are the maximal elements of a list of them and bases in their `N`. -/
private theorem maxBases_closure (ho : o.Total) {bs L : List Term}
    (hs : bs.Pairwise fun a b => Term.cmp o a b = .lt) (hu : unnested bs = true)
    (hb : ∀ b ∈ bs, b ∈ L) (hL : ∀ x ∈ L, x ∈ bs ∨ ∃ b ∈ bs, x ∈ b.negBases) :
    maxBases o L = bs := by
  have hT := termCmp_total o ho; have := hT.1
  refine eq_of_pairwise_lt (strictlyIncreasing_iff_pairwise.1 (maxBases_strictlyIncreasing hT L))
    hs fun x => ?_
  rw [mem_maxBases']; have hu' := unnested_iff.1 hu
  refine ⟨fun ⟨hx, hn⟩ => ?_, fun hx => ⟨hb x hx, fun c hc hxc => ?_⟩⟩
  · rcases hL x hx with h | ⟨b, hb', h⟩; exacts [h, absurd h (hn b (hb b hb'))]
  · rcases hL c hc with h | ⟨b, hb', h⟩
    exacts [hu' x hx c h hxc, hu' x hx b hb' (negBases_trans h hxc)]

/-- A base of `N` of a canonical term has a canonical reciprocal and is no constant. -/
private theorem recip_canon {t b : Term} (ht : Term.Canonical o me R t) (hb : b ∈ t.negBases) :
    Term.Canonical o me R b.reciprocal ∧ b.isConstant = false := by
  obtain ⟨k, hk, hc, hn⟩ := mem_negBases.1 hb
  obtain ⟨hp, hb'⟩ := canon_power.1 (canonical_node ht hn)
  obtain ⟨h1, h2, -, -, h5, -⟩ := canonicalPower_iff.1 hp
  refine ⟨canon_power.2 ⟨canonicalPower_iff.2 ⟨h1, h2, by omega, fun u n _ => by omega,
    fun c j e => ?_, fun _ => by omega⟩, hb'⟩, hc⟩
  have := mergeCondition_false.1 (h5 c j e).1
  exact ⟨mergeCondition_false.2 ⟨this.1, by omega⟩, .inl (by omega)⟩

/-- Powers with one exponent compare as their bases. -/
private theorem cmp_power (b c : Term) (k : ℤ) :
    Term.cmp o (.power b k) (.power c k) = Term.cmp o b c := by
  simp only [Term.cmp, Term.firstDifference]
  cases Term.firstDifference o b c <;> simp [Difference.andThen, Difference.ofOrdering]

/-- The reciprocal of a base that `reciprocalBase?` reads. -/
private theorem recipBase_eq {f b : Term} (h : f.reciprocalBase? = some b) :
    f = b.reciprocal ∧ b.isConstant = false := by
  unfold Term.reciprocalBase? at h; split at h
  · split_ifs at h with hc; cases h; exact ⟨rfl, by simpa using hc⟩
  · cases h

/-- The reciprocals that `mapM reciprocalBase?` reads. -/
private theorem mapM_recip_eq : ∀ {fs bs : List Term}, fs.mapM Term.reciprocalBase? = some bs →
    fs = bs.map Term.reciprocal ∧ ∀ b ∈ bs, b.isConstant = false
  | [], bs, h => by simp at h; subst h; simp
  | f :: fs, bs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs', hbs', rfl⟩ := h
    obtain ⟨e, hc⟩ := mapM_recip_eq hbs'
    obtain ⟨rfl, hcb⟩ := recipBase_eq hb
    exact ⟨by rw [e]; rfl, List.forall_mem_cons.2 ⟨hcb, hc⟩⟩

/-- `mapM reciprocalBase?` reads the bases of reciprocals of bases that are no constants. -/
private theorem mapM_recip : ∀ {bs : List Term}, (∀ b ∈ bs, b.isConstant = false) →
    (bs.map Term.reciprocal).mapM Term.reciprocalBase? = some bs
  | [], _ => rfl
  | b :: bs, h => by
    simp [Term.reciprocal, Term.reciprocalBase?, h b (by simp),
      mapM_recip (fun x hx => h x (.tail _ hx))]

/-- Reciprocals of sorted unnested bases, no constants, with the coefficient 0 or 1. -/
private theorem canon_recips (ho : o.Total) {bs : List Term} {c : ℚ} (hc : c = 0 ∨ c = 1)
    (hs : bs.Pairwise fun a b => Term.cmp o a b = .lt) (hu : unnested bs = true)
    (hb : ∀ b ∈ bs, Term.Canonical o me R b.reciprocal ∧ b.isConstant = false)
    (hm : 2 ≤ bs.length ∨ (bs ≠ [] ∧ c ≠ 1)) :
    Term.Canonical o me R (.product c (bs.map Term.reciprocal)) := by
  refine canon_product.2 ⟨?_, by simpa using fun b hb' => (hb b hb').1⟩
  have := (keyCmp_total o ho).1
  have hk : strictlyIncreasing (Key.cmp o) ((bs.map Term.reciprocal).map Term.key) = true := by
    rw [strictlyIncreasing_iff_pairwise, List.map_map, List.pairwise_map]
    exact hs.imp_of_mem fun ha hb' h => by
      simp [Term.reciprocal, Term.key, Key.of, Key.cmp, (hb _ ha).2, (hb _ hb').2, h]
  unfold canonicalProduct
  simp only [Bool.and_eq_true, List.all_eq_true, hk]
  refine ⟨⟨⟨fun f hf => ?_, trivial⟩, ?_⟩, ?_⟩
  · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hf; rfl
  · rcases bs with _ | ⟨b, _ | ⟨b', bs⟩⟩
    · simp at hm
    · simp at hm; simp [hm, Term.reciprocal]
    · rfl
  · rcases hc with rfl | rfl
    · simp [mapM_recip fun b h => (hb b h).2, hu]
    · simp [List.filterMap_map, Term.reciprocal, Term.oneBase?, unnested]

/-- The zero witness of the maximal elements of bases of `N` of canonical terms. -/
private theorem canon_zeroWitness (ho : o.Total) {L : List Term}
    (hL : ∀ b ∈ L, Term.Canonical o me R b.reciprocal ∧ b.isConstant = false) :
    Term.Canonical o me R (zeroWitness (maxBases o L)) := by
  have := (termCmp_total o ho).1
  unfold zeroWitness; split; · exact canonical_number 0
  rename_i hne
  exact canon_recips ho (.inl rfl)
    (strictlyIncreasing_iff_pairwise.1 (maxBases_strictlyIncreasing (termCmp_total o ho) L))
    (unnested_maxBases L) (fun b hb => hL b (maxBases_subset hb))
    (.inr ⟨fun e => hne (by rw [e]; rfl), zero_ne_one⟩)

/-- The core of a witness monomial: canonical, and it names its bases. -/
private theorem canon_witnessCore (ho : o.Total) {bs : List Term} (hne : bs ≠ [])
    (hs : bs.Pairwise fun a b => Term.cmp o a b = .lt) (hu : unnested bs = true)
    (hb : ∀ b ∈ bs, Term.Canonical o me R b.reciprocal ∧ b.isConstant = false) :
    Term.Canonical o me R (witnessCore bs) ∧ witnessBases? (witnessCore bs) = some bs ∧
      (witnessCore bs).coreFactors = bs.map Term.reciprocal := by
  rcases bs with _ | ⟨b, _ | ⟨b', bs⟩⟩
  · exact absurd rfl hne
  · refine ⟨(hb b (by simp)).1, ?_, rfl⟩
    simp [witnessCore, witnessBases?, Term.reciprocal, Term.reciprocalBase?, (hb b (by simp)).2]
  · refine ⟨canon_recips ho (.inr rfl) hs hu hb (.inl (by simp)), ?_, rfl⟩
    show witnessBases? (.product 1 _) = _
    rw [witnessBases?, ite_eq_left rfl]; exact mapM_recip fun b h => (hb b h).2

/-- The one of a base of `N` of a canonical term. -/
private theorem canon_oneOf {b : Term} (h : Term.Canonical o me R b.reciprocal)
    (hc : b.isConstant = false) : Term.Canonical o me R b.oneOf :=
  canon_power.2 ⟨by simp [canonicalPower, Term.factorOk, Term.imaginaryUnit, rootOf,
    mergeCondition, hc], h⟩

/-! ## The shape of products -/

/-- The ones condition of a product with a coefficient other than 0. -/
private def onesOk (fs : List Term) : Bool :=
  unnested (fs.filterMap Term.oneBase?) && (fs.filterMap Term.oneBase?).all fun b =>
    !(Term.negBasesList (fs.filter fun f => !f.isOne)).contains b

/-- The ones condition by membership. -/
private theorem onesOk_iff {fs : List Term} : onesOk fs = true ↔
    (∀ b ∈ fs.filterMap Term.oneBase?, ∀ c ∈ fs.filterMap Term.oneBase?, b ∉ c.negBases) ∧
      ∀ b ∈ fs.filterMap Term.oneBase?, ∀ f ∈ fs, f.isOne = false → b ∉ f.negBases := by
  simp only [onesOk, Bool.and_eq_true, unnested_iff, List.all_eq_true, List.contains_eq_mem,
    Bool.not_eq_true', decide_eq_false_iff_not, mem_negBasesList, List.mem_filter, not_exists,
    not_and, and_imp]

/-- The one of a base. -/
private theorem oneBase_eq {t b : Term} (h : t.oneBase? = some b) : t = b.oneOf := by
  unfold Term.oneBase? at h; split at h <;> simp_all [Term.oneOf]

/-- One factor satisfies the ones condition. -/
private theorem onesOk_single (t : Term) : onesOk [t] = true := by
  rcases h : t.oneBase? with _ | b
  · simp [onesOk, h, unnested]
  · rw [oneBase_eq h]
    simp [onesOk, Term.oneOf, Term.isOne, Term.negBasesList, unnested, Term.oneBase?, not_mem_self]

/-- The shape of a product with a coefficient other than 0, from its parts. -/
private theorem canonicalProduct_of {c : ℚ} {fs : List Term} (hc : c ≠ 0)
    (hf : ∀ f ∈ fs, f.factorOk = true) (hk : strictlyIncreasing (Key.cmp o) (fs.map Term.key))
    (hm : 2 ≤ fs.length ∨ ∃ f, fs = [f] ∧ c ≠ 1 ∧ ∀ a ms, f ≠ .sum a ms)
    (hon : onesOk fs = true) : canonicalProduct o c fs = true := by
  unfold canonicalProduct
  rw [ite_eq_right hc]
  simp only [onesOk, Bool.and_eq_true, List.all_eq_true] at hon
  simp only [Bool.and_eq_true, List.all_eq_true, hk]
  refine ⟨⟨⟨hf, trivial⟩, ?_⟩, hon⟩
  rcases hm with h | ⟨f, rfl, h1, hs⟩
  · rcases fs with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> simp at h ⊢
  · cases f <;> simp_all

/-- The ones condition of a canonical product; reciprocals over unnested bases for the coefficient 0. -/
private theorem onesOk_of {c : ℚ} {fs : List Term} (h : canonicalProduct o c fs = true) :
    (c = 0 → ∃ bs, fs.mapM Term.reciprocalBase? = some bs ∧ unnested bs = true) ∧ onesOk fs = true := by
  unfold canonicalProduct at h
  simp only [Bool.and_eq_true] at h
  split_ifs at h with hc
  · have h2 := h.2; split at h2; swap; · simp at h2
    rename_i bs hbs
    have : fs.filterMap Term.oneBase? = [] := List.filterMap_eq_nil_iff.2 fun f hf => by
      rw [(mapM_recip_eq hbs).1] at hf
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hf; cases b <;> simp [Term.reciprocal, Term.oneBase?]
    exact ⟨fun _ => ⟨bs, hbs, h2⟩, by simp [onesOk, this, unnested]⟩
  · exact ⟨fun e => absurd e hc, h.2⟩

/-- A product with two or more factors keeps its shape under any coefficient other than 0. -/
private theorem canonicalProduct_coef {c d : ℚ} {fs : List Term} (h : canonicalProduct o c fs)
    (hl : 2 ≤ fs.length) (hd : d ≠ 0) : canonicalProduct o d fs = true := by
  have h' := h; unfold canonicalProduct at h'
  simp only [Bool.and_eq_true, List.all_eq_true] at h'
  exact canonicalProduct_of hd h'.1.1.1 h'.1.1.2 (.inl hl) (onesOk_of h).2

/-- One factor that is no sum, with a coefficient other than 0 and 1. -/
private theorem canonicalProduct_single {a : ℚ} {t : Term} (ha : a ≠ 0) (h1 : a ≠ 1)
    (hf : t.factorOk = true) (hs : ∀ c ms, t ≠ .sum c ms) : canonicalProduct o a [t] = true :=
  canonicalProduct_of ha (by simpa using hf) (by simp [strictlyIncreasing])
    (.inr ⟨t, rfl, h1, hs⟩) (onesOk_single t)

/-! ## Sums -/

/-- The cores that canonical operands give are canonical. -/
private theorem sumParts_canon {ts : List Term} (h : ∀ t ∈ ts, Term.Canonical o me R t) :
    ∀ m ∈ (sumParts ts).2, Term.Canonical o me R m.2 := by
  induction ts with
  | nil => simp [sumParts]
  | cons t ts ih =>
    rw [show t :: ts = [t] ++ ts from rfl, Sums.sumParts_append]
    intro m hm
    rcases List.mem_append.1 hm with hm | hm
    · have ht := h t (by simp)
      cases t with
      | sum c ms => simp only [sumParts, List.append_nil] at hm; exact (canon_sum.1 ht).2 m hm
      | product c fs =>
        simp only [sumParts, List.mem_singleton] at hm; subst hm
        obtain ⟨hp, hf⟩ := canon_product.1 ht
        rcases fs with _ | ⟨f, _ | ⟨g, fs⟩⟩
        · simp [canonicalProduct] at hp
        · exact hf f (by simp)
        · exact canon_product.2 ⟨canonicalProduct_coef hp (by simp) one_ne_zero, hf⟩
      | number => simp [sumParts] at hm
      | _ => simp only [sumParts, List.mem_singleton] at hm; subst hm; exact ht
    · exact ih (fun t ht => h t (by simp [ht])) m hm

/-- The product of a coefficient other than 0 and 1 and the factors of a canonical core. -/
private theorem canon_coreProduct {a : ℚ} {t : Term} (ha : a ≠ 0) (h1 : a ≠ 1)
    (ht : Term.Canonical o me R t) (hc : t.coreOk = true) :
    Term.Canonical o me R (.product a t.coreFactors) := by
  cases t with
  | product b fs =>
    obtain ⟨hp, hf⟩ := canon_product.1 ht
    simp only [Term.coreOk, beq_iff_eq] at hc; subst hc
    refine canon_product.2 ⟨canonicalProduct_coef hp ?_ ha, hf⟩
    rcases fs with _ | ⟨f, _ | ⟨g, fs⟩⟩ <;> simp [canonicalProduct, Term.coreFactors] at hp ⊢
  | number | sum | condition => simp [Term.coreOk] at hc
  | _ => exact canon_product.2 ⟨canonicalProduct_single ha h1 rfl nofun,
      by simpa [Term.coreFactors] using ht⟩

/-- `N` of a term is `N` of its factors as a core. -/
private theorem negBases_coreFactors (t x : Term) :
    x ∈ t.negBases ↔ x ∈ Term.negBasesList t.coreFactors := by
  cases t <;> simp [Term.coreFactors, Term.negBases, Term.negBasesList]

/-- The monomials of a cancelled merge of canonical cores, and its shape as a sum node. -/
private theorem cancel_canon (ho : o.Total) {ms : List (ℚ × Term)}
    (hc : ∀ m ∈ ms, Term.Canonical o me R m.2 ∧ m.2.coreOk = true) :
    (∀ m ∈ cancelMonomials o (mergeMonomials o ms), Term.Canonical o me R m.2 ∧
      m.2.coreOk = true ∧ (m.1 = 0 → Term.Canonical o me R (.product 0 m.2.coreFactors))) ∧
    ∀ c, 2 ≤ (cancelMonomials o (mergeMonomials o ms)).length + (if c = 0 then 0 else 1) →
      canonicalSum o c (cancelMonomials o (mergeMonomials o ms)) = true := by
  have hT := termCmp_total o ho; have := hT.1
  have hz := Sums.filter_zero_cancelMonomials o (mergeMonomials o ms)
  have hM : ∀ m ∈ mergeMonomials o ms, Term.Canonical o me R m.2 ∧ m.2.coreOk = true :=
    fun m hm => by
      obtain ⟨n, hn, e⟩ := List.mem_map.1 ((mem_mergeMonomials hT).1 hm).1; exact e ▸ hc n hn
  have hs := mergeMonomials_strictlyIncreasing hT ms
  generalize mergeMonomials o ms = M at hz hM hs
  rw [Sums.cancelMonomials_eq] at hz ⊢
  have hBb : ∀ b ∈ Sums.cancelBases o M, (Term.Canonical o me R b.reciprocal ∧
      b.isConstant = false) ∧ b ∉ Term.negBasesPairs (M.filter fun m => decide (m.1 ≠ 0)) := by
    intro b hb
    obtain ⟨h1, h2⟩ := mem_uncovered.1 (maxBases_subset hb)
    obtain ⟨m, hm, hbm⟩ := mem_negBasesPairs.1 h1
    exact ⟨recip_canon (hM m (List.mem_filter.1 hm).1).1 hbm, h2⟩
  have hrest : ∀ m ∈ M.filter fun m => decide (m.1 ≠ 0), m ∈ M ∧ m.1 ≠ 0 :=
    fun m hm => by simpa using List.mem_filter.1 hm
  have hrs := strictlyIncreasing_filter_map hs fun m => decide (m.1 ≠ 0)
  have hold : ∀ m ∈ M.filter fun m => decide (m.1 ≠ 0), Term.Canonical o me R m.2 ∧
      m.2.coreOk = true ∧ (m.1 = 0 → Term.Canonical o me R (.product 0 m.2.coreFactors)) :=
    fun m hm => ⟨(hM m (hrest m hm).1).1, (hM m (hrest m hm).1).2, fun h => absurd h (hrest m hm).2⟩
  split_ifs at hz ⊢ with hB0
  · refine ⟨hold, fun c hl => ?_⟩
    unfold canonicalSum; simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    rw [hz]; exact ⟨⟨⟨hl, fun m hm => (hold m hm).2.1⟩, hrs⟩, rfl⟩
  have hBs := strictlyIncreasing_iff_pairwise.1 (maxBases_strictlyIncreasing hT
    (uncovered (Term.negBasesPairs (M.filter fun m => decide (m.1 = 0)))
      (Term.negBasesPairs (M.filter fun m => decide (m.1 ≠ 0)))))
  have hBu := unnested_maxBases (o := o) (uncovered (Term.negBasesPairs
    (M.filter fun m => decide (m.1 = 0))) (Term.negBasesPairs (M.filter fun m => decide (m.1 ≠ 0))))
  rw [← Sums.cancelBases] at hBs hBu
  generalize Sums.cancelBases o M = B at hB0 hBb hz hBs hBu ⊢
  generalize hR : M.filter (fun m => decide (m.1 ≠ 0)) = rest at hBb hrest hrs hold hz ⊢
  obtain ⟨hw, hwb, hwf⟩ := canon_witnessCore ho hB0 hBs hBu fun b hb => (hBb b hb).1
  have hmem : ∀ m, m ∈ insertBy (monomialCmp o) (0, witnessCore B) rest ↔
      m = (0, witnessCore B) ∨ m ∈ rest := fun m => by
    rw [(perm_insertBy _ _ _).mem_iff, List.mem_cons]
  have hwr : witnessCore B ∉ rest.map Prod.snd := fun h => by
    obtain ⟨m, hm, e⟩ := List.mem_map.1 h
    obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil B hB0
    refine (hBb b hb).2 (mem_negBasesPairs.2 ⟨m, hm, ?_⟩)
    rw [e, negBases_coreFactors, hwf, mem_negBases_reciprocals fun b h => (hBb b h).1.2]
    exact ⟨b, hb, .inl rfl⟩
  refine ⟨fun m hm => ?_, fun c hl => ?_⟩
  · rcases (hmem m).1 hm with rfl | hm
    · refine ⟨hw, (Sums.coreShape_witnessCore B).1, fun _ => ?_⟩
      rw [hwf]; exact canon_recips ho (.inl rfl) hBs hBu (fun b hb => (hBb b hb).1)
        (.inr ⟨hB0, zero_ne_one⟩)
    · exact hold m hm
  unfold canonicalSum; simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  rw [hz]
  refine ⟨⟨⟨hl, fun m hm => ?_⟩, strictlyIncreasing_insertBy_map hT Prod.snd hrs hwr⟩, ?_⟩
  · rcases (hmem m).1 hm with rfl | hm
    exacts [(Sums.coreShape_witnessCore B).1, (hold m hm).2.1]
  simp only [hwb, Bool.and_eq_true, hBu, List.all_eq_true, List.contains_eq_mem,
    Bool.not_eq_true', decide_eq_false_iff_not, true_and]
  intro b hb hbh
  obtain ⟨m, hm, hbm⟩ := mem_negBasesPairs.1 hbh
  obtain ⟨hm, h0⟩ := List.mem_filter.1 hm
  rcases (hmem m).1 hm with rfl | hm
  · simp at h0
  · exact (hBb b hb).2 (mem_negBasesPairs.2 ⟨m, hm, hbm⟩)

/-- A sum of canonical operands. -/
private theorem mkSum_ok (ho : o.Total) {ts : List Term} (h : ∀ t ∈ ts, Term.Canonical o me R t) :
    OK (Term.Canonical o me R) (mkSum o ts) := by
  unfold mkSum; split; · simp [OK]
  rename_i hv; simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at hv
  obtain ⟨hL, hS⟩ := cancel_canon ho (ms := (sumParts ts).2) fun m hm =>
    ⟨sumParts_canon h m hm, (Sums.coreShape_sumParts h hv m hm).1⟩
  show Term.Canonical o me R (assembleSum _ _)
  generalize cancelMonomials o (mergeMonomials o (sumParts ts).2) = L at hL hS
  generalize (sumParts ts).1 = c
  have hsum : 2 ≤ L.length + (if c = 0 then 0 else 1) → Term.Canonical o me R (.sum c L) :=
    fun hl => canon_sum.2 ⟨hS c hl, fun m hm => (hL m hm).1⟩
  rcases L with _ | ⟨⟨a, t⟩, _ | ⟨n, L⟩⟩
  · exact canonical_number c
  · have ht := hL (a, t) (by simp)
    simp only [assembleSum]
    split_ifs with h0 h1
    · exact ht.1
    · by_cases ha : a = 0
      · subst ha; exact ht.2.2 rfl
      · exact canon_coreProduct ha h1 ht.1 ht.2.1
    · exact hsum (by simp [h0])
  · exact hsum (by simp only [List.length_cons]; split <;> omega)

/-- A canonical sum scaled by a number other than 0. -/
private theorem canon_scale {a c : ℚ} {ms : List (ℚ × Term)} (ha : a ≠ 0)
    (h : Term.Canonical o me R (.sum c ms)) : Term.Canonical o me R (scaleSum a c ms) := by
  obtain ⟨hs, hm⟩ := canon_sum.1 h
  refine canon_sum.2 ⟨?_, fun m h' => by obtain ⟨n, hn, rfl⟩ := List.mem_map.1 h'; exact hm n hn⟩
  unfold canonicalSum at hs ⊢
  simp only [List.length_map, mul_eq_zero, ha, false_or, List.all_map, List.map_map,
    List.filter_map, Function.comp_def] at hs ⊢
  simp only [Bool.and_eq_true] at hs ⊢
  refine ⟨hs.1, ?_⟩
  have := hs.2; revert this
  generalize ms.filter (fun m => decide (m.1 = 0)) = Z
  rcases Z with _ | ⟨⟨x, w⟩, _ | ⟨_, _⟩⟩ <;> simp [negBasesPairs_map, ha]

/-- The primitive part of a canonical sum: canonical, a factor, of content 1. -/
private theorem canon_prim {c : ℚ} {ms : List (ℚ × Term)}
    (h : Term.Canonical o me R (.sum c ms)) : Term.Canonical o me R (primitivePart c ms) ∧
      (primitivePart c ms).factorOk = true := by
  have hne := sumContent_ne_zero (canon_sum.1 h).1
  exact ⟨canon_scale (inv_ne_zero hne) h,
    by simp [primitivePart, scaleSum, Term.factorOk, sumContent_scale (inv_ne_zero hne), hne]⟩

/-! ## Products -/

/-- An item for the rounds: a canonical factor that is no one, negative over a negative power. -/
private def ItemOk (o : Orders) (me : ℕ) (R : RegistryRules) (x : Term × ℤ) : Prop :=
  Term.Canonical o me R x.1 ∧ x.1.factorOk = true ∧ x.1.isOne = false ∧
    ∀ c j, x.1 = .power c j → j < 0 ∧ x.2 < 0

/-- Parts whose items can enter the rounds and whose ones are canonical. -/
private def PartsOk (o : Orders) (me : ℕ) (R : RegistryRules) (p : ProductParts) : Prop :=
  (∀ x ∈ p.items, ItemOk o me R x) ∧ ∀ t ∈ p.ones, Term.Canonical o me R t ∧ t.isOne = true

/-- `ItemOk` depends only on the key of the item. -/
private theorem ItemOk.key {x y : Term × ℤ} (h : Key.of x.1 x.2 = Key.of y.1 y.2)
    (hy : ItemOk o me R y) : ItemOk o me R x := by
  obtain ⟨b, k⟩ := x; obtain ⟨b', k'⟩ := y
  simp only [Key.of, Key.mk.injEq] at h; obtain ⟨rfl, h⟩ := h
  refine ⟨hy.1, hy.2.1, hy.2.2.1, fun c j e => ?_⟩
  obtain ⟨h1, h2⟩ := hy.2.2.2 c j e; subst e
  exact ⟨h1, by simp_all [Term.isConstant]⟩

/-- A one is a power 0 of a reciprocal. -/
private theorem isOne_eq {t : Term} (h : t.isOne = true) : ∃ b : Term, t = b.oneOf := by
  unfold Term.isOne at h; split at h; exacts [⟨_, rfl⟩, by cases h]

/-- A power with an exponent other than 0 is no one. -/
private theorem power_not_one {b : Term} {k : ℤ} (hk : k ≠ 0) :
    (Term.power b k).isOne = false ∧ (Term.power b k).oneBase? = none := by
  cases b <;> simp [Term.isOne, Term.oneBase?, hk]

/-- A canonical power is a one exactly for the exponent 0. -/
private theorem power_isOne {b : Term} {k : ℤ} (h : Term.Canonical o me R (.power b k)) :
    (Term.power b k).isOne = true ↔ k = 0 := by
  obtain ⟨-, -, -, -, h5, h6⟩ := canonicalPower_iff.1 (canon_power.1 h).1
  refine ⟨fun e => (by by_contra hk; rw [(power_not_one hk).1] at e; cases e), fun hk => ?_⟩
  subst hk; cases b with
  | power c j => obtain ⟨-, h | ⟨rfl, -⟩⟩ := h5 c j rfl; exacts [absurd rfl h, rfl]
  | _ => exact absurd rfl (h6 nofun)

/-- The parts of a folded list of parts. -/
private theorem PartsOk.foldl {ps : List ProductParts} {p : ProductParts}
    (h : PartsOk o me R p) (hps : ∀ r ∈ ps, PartsOk o me R r) :
    PartsOk o me R (ps.foldl ProductParts.append p) := by
  rw [foldl_append]
  refine ⟨fun x hx => ?_, fun t ht => ?_⟩
  · simp only [List.mem_append, List.mem_flatten, List.mem_map] at hx
    rcases hx with hx | ⟨_, ⟨r, hr, rfl⟩, hx⟩; exacts [h.1 x hx, (hps r hr).1 x hx]
  · simp only [List.mem_append, List.mem_flatten, List.mem_map] at ht
    rcases ht with ht | ⟨_, ⟨r, hr, rfl⟩, ht⟩; exacts [h.2 t ht, (hps r hr).2 t ht]

/-- The parts of a positive power of a canonical value that is no number and no product. -/
private theorem itemParts_ok {t : Term} {q : ℤ} (hq : 0 < q) (ht : Term.Canonical o me R t)
    (hv : t.isCondition = false) (hn : ∀ r, t ≠ .number r) (hp : ∀ c fs, t ≠ .product c fs) :
    OK (PartsOk o me R) (itemParts me q t) := by
  cases t with
  | sum c ms =>
    exact ⟨by simpa using ⟨(canon_prim ht).1, (canon_prim ht).2, rfl, nofun⟩, by simp⟩
  | power b j =>
    obtain ⟨hcp, hb⟩ := canon_power.1 ht
    obtain ⟨h1, -, -, -, h5, -⟩ := canonicalPower_iff.1 hcp
    simp only [itemParts]; split
    · rename_i hj; subst hj; exact ⟨by simp, by simpa using ⟨ht, (power_isOne ht).2 rfl⟩⟩
    · rename_i hj
      refine OK.check ⟨fun x hx => ?_, by simp⟩
      obtain rfl : x = _ := by simpa using hx
      refine ⟨hb, h1, ?_, fun c i e => ?_⟩
      · cases e : b.isOne; · rfl
        obtain ⟨c, rfl⟩ := isOne_eq e
        exact absurd (mergeCondition_false.1 (h5 _ 0 rfl).1).1 (lt_irrefl 0)
      · have := mergeCondition_false.1 (h5 c i e).1
        exact ⟨this.1, mul_neg_of_neg_of_pos (by omega) hq⟩
  | number r => exact absurd rfl (hn r)
  | product c fs => exact absurd rfl (hp c fs)
  | condition => simp [Term.isCondition] at hv
  | _ => exact ⟨by simpa using ⟨ht, rfl, rfl, nofun⟩, by simp⟩

/-- A factor is no number, product or condition. -/
private theorem factorOk_kind {f : Term} (h : f.factorOk = true) :
    f.isCondition = false ∧ (∀ r, f ≠ .number r) ∧ ∀ c fs, f ≠ .product c fs := by
  cases f <;> simp_all [Term.factorOk, Term.isCondition]

/-- The factors of a canonical product. -/
private theorem factors_ok {c : ℚ} {fs : List Term} (h : Term.Canonical o me R (.product c fs)) :
    ∀ f ∈ fs, Term.Canonical o me R f ∧ f.factorOk = true := by
  obtain ⟨hp, hf⟩ := canon_product.1 h
  simp only [canonicalProduct, Bool.and_eq_true, List.all_eq_true] at hp
  exact fun f h => ⟨hf f h, hp.1.1.1 f h⟩

/-- The parts of a positive power of a canonical value. -/
private theorem factorParts_ok {t : Term} {q : ℤ} (hq : 0 < q) (ht : Term.Canonical o me R t)
    (hv : t.isCondition = false) : OK (PartsOk o me R) (factorParts me q t) := by
  cases t with
  | number r => exact ⟨by simp, by simp⟩
  | product c fs =>
    have hf := factors_ok ht
    exact (OK.mapM fun f h => itemParts_ok hq (hf f h).1 (factorOk_kind (hf f h).2).1
      (factorOk_kind (hf f h).2).2.1 (factorOk_kind (hf f h).2).2.2).bind fun ps hps =>
        OK.pure (PartsOk.foldl ⟨by simp, by simp⟩ hps)
  | _ => exact itemParts_ok hq ht hv nofun nofun

/-- The parts of canonical values. -/
private theorem productParts_ok {ts : List Term} (h : ∀ t ∈ ts, Term.Canonical o me R t)
    (hv : ∀ t ∈ ts, t.isCondition = false) : OK (PartsOk o me R) (productParts me ts) :=
  (OK.mapM fun t ht => factorParts_ok one_pos (h t ht) (hv t ht)).bind fun _ hps =>
    OK.pure (PartsOk.foldl ⟨by simp [ProductParts.unit], by simp [ProductParts.unit]⟩ hps)

/-- A reduced item of the rounds keeps the parts that can enter them. -/
private theorem reduceItem_ok {x : Term × ℤ} {r : ProductParts × List (Term × ℤ)}
    (hx : ItemOk o me R x) (h : reduceItem me x = .value r) :
    PartsOk o me R r.1 ∧ ∀ y ∈ r.2, ItemOk o me R y := by
  obtain ⟨b, k⟩ := x
  have hb : ∀ k', (∀ c j, b ≠ .power c j) → ItemOk o me R (b, k') :=
    fun _ hb => ⟨hx.1, hx.2.1, hx.2.2.1, fun c j e => absurd e (hb c j)⟩
  rw [reduceItem] at h; unfold checkExponent at h
  split at h; · cases h
  split at h; · cases h; simp [PartsOk, ProductParts.unit]
  split at h
  · cases h; rename_i hi; subst hi
    refine ⟨⟨fun y hy => ?_, by simp⟩, by simp⟩
    dsimp only at hy; split_ifs at hy; swap; · simp at hy
    obtain rfl : y = _ := by simpa using hy
    exact hb 1 fun c j e => by simp [Term.imaginaryUnit] at e
  rcases hr : rootOf b with _ | ⟨u, n⟩ <;> simp only [hr] at h
  · cases h; exact ⟨⟨by simpa using hx, by simp⟩, by simp⟩
  have hpw : ∀ c j, b ≠ .power c j := fun c j e => by subst e; simp [rootOf] at hr
  split at h
  · obtain ⟨p, hp, h⟩ := bind_eq_value.1 h; cases h
    obtain ⟨hu, huv⟩ := root_radicand hx.1 hr
    have h2 := (rootOf_some hr).1
    have hpk := factorParts_ok (q := k / n) (Int.le_ediv_of_mul_le (by omega) (by omega)) hu huv
    rw [hp] at hpk
    refine ⟨⟨fun y hy => ?_, hpk.2⟩, hpk.1⟩
    dsimp only at hy; split_ifs at hy; · simp at hy
    obtain rfl : y = _ := by simpa using hy
    exact hb _ hpw
  · cases h; exact ⟨⟨by simpa using hx, by simp⟩, by simp⟩

/-- The rounds keep the parts that can enter them. -/
private theorem settle_ok (ho : o.Total) : ∀ {fuel : ℕ} {p p' : ProductParts},
    settleItems o me fuel p = .value p' → PartsOk o me R p → PartsOk o me R p'
  | 0, _, _, h, _ => by cases h
  | fuel + 1, p, p', h, hp => by
    have hK := keyCmp_total o ho
    rw [settleItems] at h
    obtain ⟨rs, hrs, h⟩ := bind_eq_value.1 h
    have hr : ∀ r ∈ rs, PartsOk o me R r.1 ∧ ∀ y ∈ r.2, ItemOk o me R y := fun r hr => by
      obtain ⟨x, hx, hxr⟩ := (mapM_mem hrs).2 r hr
      obtain ⟨y, hy, e⟩ := List.mem_map.1 ((mem_mergeItems hK).1 hx).1
      exact reduceItem_ok (ItemOk.key e.symm (hp.1 y hy)) hxr
    have hs : PartsOk o me R (rs.foldl (fun acc r => acc.append r.1) ⟨p.coefficient, [], p.ones⟩) := by
      rw [← List.foldl_map (f := Prod.fst)]
      exact PartsOk.foldl ⟨by simp, hp.2⟩ fun r h => by
        obtain ⟨r', h', rfl⟩ := List.mem_map.1 h; exact (hr r' h').1
    dsimp only at h; split at h
    · cases h; exact hs
    refine settle_ok ho h ⟨fun x hx => ?_, hs.2⟩
    rcases List.mem_append.1 hx with hx | hx; · exact hs.1 x hx
    simp only [List.mem_flatten, List.mem_map] at hx
    obtain ⟨_, ⟨r, hr', rfl⟩, hx⟩ := hx; exact (hr r hr').2 x hx

/-- `buildProduct` settles the parts and assembles them. -/
private theorem build_eq (o : Orders) (me : ℕ) (p : ProductParts) :
    buildProduct o me p = settleItems o me (Term.depthList (p.items.map Prod.fst) + 1) p >>=
      fun s => pure (Products.finish o s) := by
  unfold buildProduct Products.finish; congr 1; funext s; dsimp only; split <;> rfl

/-- The product of a coefficient other than 0 and factors with increasing keys and the ones condition. -/
private theorem canon_assemble {c : ℚ} {G : List Term} (hc : c ≠ 0)
    (hG : ∀ f ∈ G, Term.Canonical o me R f ∧ f.factorOk = true)
    (hk : strictlyIncreasing (Key.cmp o) (G.map Term.key)) (hon : onesOk G = true) :
    Term.Canonical o me R (assembleProduct c G) := by
  rcases G with _ | ⟨f, _ | ⟨g, G⟩⟩
  · exact canonical_number c
  · obtain ⟨hf, hfo⟩ := hG f (by simp)
    simp only [assembleProduct]; split_ifs with h1; · exact hf
    cases f with
    | sum a ms => exact canon_scale hc hf
    | _ => exact canon_product.2 ⟨canonicalProduct_of hc (by simpa using hfo) hk
        (.inr ⟨_, rfl, h1, nofun⟩) hon, by simpa using hf⟩
  · exact canon_product.2 ⟨canonicalProduct_of hc (fun f h => (hG f h).2) hk (.inl (by simp)) hon,
      fun f h => (hG f h).1⟩

/-- The power 0 of a canonical term. -/
private theorem canon_powerZero (ho : o.Total) {t : Term} (ht : Term.Canonical o me R t) :
    Term.Canonical o me R (powerZero o t) := by
  have := (termCmp_total o ho).1; have := (keyCmp_total o ho).1
  have hb : ∀ b ∈ maxBases o t.negBases, Term.Canonical o me R b.reciprocal ∧
      b.isConstant = false := fun b hb => recip_canon ht (maxBases_subset hb)
  have hs := strictlyIncreasing_iff_pairwise.1
    (maxBases_strictlyIncreasing (termCmp_total o ho) t.negBases)
  have hu := unnested_maxBases (o := o) t.negBases
  unfold powerZero; generalize maxBases o t.negBases = bs at hb hs hu
  have e1 : ∀ l : List Term, (l.map Term.oneOf).filterMap Term.oneBase? = l := fun l => by
    induction l <;> simp_all [Term.oneOf, Term.oneBase?]
  have hA := canon_assemble (o := o) (me := me) (R := R) one_ne_zero (G := bs.map Term.oneOf)
    (by simpa using fun b h => ⟨canon_oneOf (hb b h).1 (hb b h).2, rfl⟩) (by
      rw [strictlyIncreasing_iff_pairwise, List.map_map, List.pairwise_map]
      exact hs.imp fun h => by simp [Term.oneOf, Term.key, Key.of, Key.cmp, cmp_power, h])
    (by simp [onesOk, e1, hu, List.filter_map, Function.comp_def, Term.oneOf, Term.isOne,
      Term.negBasesList])
  rcases bs with _ | ⟨b, _ | ⟨b', bs⟩⟩ <;> simpa [assembleProduct] using hA

/-- A term that is no one is no one's power 0. -/
private theorem oneBase_none {t : Term} (h : t.isOne = false) : t.oneBase? = none := by
  rcases e : t.oneBase? with _ | b; · rfl
  rw [oneBase_eq e] at h; simp [Term.oneOf, Term.isOne] at h

/-- The factor of a settled item that can enter the rounds. -/
private theorem itemFactor_ok {x : Term × ℤ} (hx : ItemOk o me R x) (h0 : x.2 ≠ 0)
    (hi : x.1 = Term.imaginaryUnit → x.2 = 1) (hr : ∀ u n, rootOf x.1 = some (u, n) → x.2 < n) :
    Term.Canonical o me R (itemFactor x) ∧ (itemFactor x).factorOk = true ∧
      (itemFactor x).key = Key.of x.1 x.2 ∧ (itemFactor x).isOne = false := by
  obtain ⟨b, k⟩ := x
  obtain ⟨hb, hf, h1, hp⟩ := hx
  unfold itemFactor; dsimp only at *; split
  · subst k; refine ⟨hb, hf, ?_, h1⟩
    cases b with
    | power c j => exact absurd (hp c j rfl).2 (by omega)
    | _ => rfl
  · rename_i hk1
    refine ⟨canon_power.2 ⟨canonicalPower_iff.2 ⟨hf, fun e => hk1 (hi e), hk1, hr,
      fun c j e => ?_, fun _ => h0⟩, hb⟩, rfl, rfl, (power_not_one h0).1⟩
    obtain ⟨hj, hk⟩ := hp c j e; exact ⟨mergeCondition_false.2 ⟨hj, hk.le⟩, .inl h0⟩

/-- The assembly of settled parts that can enter the rounds is canonical. -/
private theorem finish_canon (ho : o.Total) {s : ProductParts} (hp : PartsOk o me R s)
    (hst : ∀ x ∈ s.items, x.2 ≠ 0 ∧ (x.1 = Term.imaginaryUnit → x.2 = 1) ∧
      ∀ u n, rootOf x.1 = some (u, n) → x.2 < n)
    (hk : strictlyIncreasing (Key.cmp o) (s.items.map fun x => Key.of x.1 x.2)) :
    Term.Canonical o me R (Products.finish o s) := by
  have hT := termCmp_total o ho; have hK := keyCmp_total o ho; have := hT.1; have := hK.1
  have hF := fun x hx => itemFactor_ok (hp.1 x hx) (hst x hx).1 (hst x hx).2.1 (hst x hx).2.2
  have hFc : ∀ f ∈ s.items.map itemFactor, Term.Canonical o me R f ∧ f.factorOk = true ∧
      f.isOne = false := fun f hf => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hf; exact ⟨(hF x hx).1, (hF x hx).2.1, (hF x hx).2.2.2⟩
  unfold Products.finish; split
  · refine canon_zeroWitness ho fun b hb => ?_
    obtain ⟨t, ht, hbt⟩ := mem_negBasesList.1 hb
    rcases List.mem_append.1 ht with ht | ht
    exacts [recip_canon (hFc t ht).1 hbt, recip_canon (hp.2 t ht).1 hbt]
  rename_i hc
  have hkF : (s.items.map itemFactor).map Term.key = s.items.map fun x => Key.of x.1 x.2 := by
    rw [List.map_map]; exact List.map_congr_left fun x hx => (hF x hx).2.2.1
  generalize s.items.map itemFactor = F at hFc hkF ⊢
  have hkept : ∀ b ∈ maxBases o (uncovered (Term.negBasesList s.ones) (Term.negBasesList F)),
      (Term.Canonical o me R b.reciprocal ∧ b.isConstant = false) ∧ b ∉ Term.negBasesList F :=
    fun b hb => by
      obtain ⟨h1, h2⟩ := mem_uncovered.1 (maxBases_subset hb)
      obtain ⟨t, ht, hbt⟩ := mem_negBasesList.1 h1
      exact ⟨recip_canon (hp.2 t ht).1 hbt, h2⟩
  have hu := unnested_iff.1 (unnested_maxBases (o := o)
    (uncovered (Term.negBasesList s.ones) (Term.negBasesList F)))
  have hks := strictlyIncreasing_iff_pairwise.1 (maxBases_strictlyIncreasing hT
    (uncovered (Term.negBasesList s.ones) (Term.negBasesList F)))
  generalize maxBases o (uncovered (Term.negBasesList s.ones) (Term.negBasesList F)) = kept
    at hkept hu hks ⊢
  have hnd : ((F ++ kept.map Term.oneOf).map Term.key).Nodup := by
    rw [List.map_append, List.nodup_append, hkF, List.map_map]
    refine ⟨nodup_of_pairwise_lt (strictlyIncreasing_iff_pairwise.1 hk),
      (nodup_of_pairwise_lt hks).map fun a b e => by simpa [Term.oneOf, Term.key, Key.of] using e,
      fun K hK K' hK' e => ?_⟩
    subst e
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hK
    obtain ⟨b, -, e⟩ := List.mem_map.1 hK'
    simp only [Function.comp_apply, Term.oneOf, Term.key, Key.of, Key.mk.injEq] at e
    have := (hp.1 x hx).2.2.2 _ _ e.1.symm
    simp [this.2, ← e.1, Term.isConstant] at e
  have hG := perm_sortBy (fun f g => Key.cmp o f.key g.key) (F ++ kept.map Term.oneOf)
  have hGs := strictlyIncreasing_sortBy_map hK Term.key hnd
  generalize sortBy (fun f g => Key.cmp o f.key g.key) (F ++ kept.map Term.oneOf) = G at hG hGs ⊢
  have hob : ∀ b ∈ G.filterMap Term.oneBase?, b ∈ kept := fun b hb => by
    obtain ⟨f, hf, e⟩ := List.mem_filterMap.1 hb
    rcases List.mem_append.1 (hG.mem_iff.1 hf) with hf | hf
    · rw [oneBase_none (hFc f hf).2.2] at e; cases e
    · obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hf; cases e; exact hb'
  refine canon_assemble hc (fun f hf => ?_) hGs (onesOk_iff.2 ⟨fun b hb c hc' =>
    hu b (hob b hb) c (hob c hc'), fun b hb f hf h1 hbf => ?_⟩)
  · rcases List.mem_append.1 (hG.mem_iff.1 hf) with hf | hf
    · exact ⟨(hFc f hf).1, (hFc f hf).2.1⟩
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hf
      exact ⟨canon_oneOf (hkept b hb).1.1 (hkept b hb).1.2, rfl⟩
  · rcases List.mem_append.1 (hG.mem_iff.1 hf) with hf | hf
    · exact (hkept b (hob b hb)).2 (mem_negBasesList.2 ⟨f, hf, hbf⟩)
    · obtain ⟨b', -, rfl⟩ := List.mem_map.1 hf; simp [Term.oneOf, Term.isOne] at h1

/-- A product of parts that can enter the rounds is canonical, or reaches the limit. -/
private theorem buildProduct_ok (ho : o.Total) {p : ProductParts} (hp : PartsOk o me R p) :
    OK (Term.Canonical o me R) (buildProduct o me p) := by
  refine OK.of_vl (Products.buildProduct_value_or_limit o ho me p) fun u hu => ?_
  rw [build_eq] at hu
  obtain ⟨s, hs, hu⟩ := bind_eq_value.1 hu
  simp only [pure_value, Result.value.injEq] at hu; subst hu
  obtain ⟨h1, h2⟩ := Settle.settleItems_items (keyCmp_total o ho) hs
  exact finish_canon ho (settle_ok ho hs hp) h1 h2

/-- A product of canonical terms. -/
private theorem mkProduct_ok (ho : o.Total) {ts : List Term}
    (h : ∀ t ∈ ts, Term.Canonical o me R t) : OK (Term.Canonical o me R) (mkProduct o me ts) := by
  unfold mkProduct; split; · simp [OK]
  rename_i hv; simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at hv
  exact (productParts_ok h hv).bind fun p hp => buildProduct_ok ho hp

/-! ## Powers and the other constructors -/

/-- The merges of a canonical factor give a canonical factor that merges no further. -/
private theorem mergePowers_ok (b : Term) : Term.Canonical o me R b → b.factorOk = true →
    ∀ k, OK (fun cj : Term × ℤ => Term.Canonical o me R cj.1 ∧ cj.1.factorOk = true ∧
      ∀ c j, cj.1 = .power c j → mergeCondition j cj.2 = false) (mergePowers me b k) := by
  induction b using term_induct with
  | power c j ih =>
    intro hb hf k
    obtain ⟨hcp, hc⟩ := canon_power.1 hb
    rw [mergePowers]; split
    · exact OK.check (ih hc (canonicalPower_iff.1 hcp).1 _)
    · rename_i hm; exact ⟨hb, hf, fun c' j' e => by cases e; simpa using hm⟩
  | number | constant | symbol | call | product | sum | condition =>
    intro hb hf k; exact ⟨hb, hf, nofun⟩

/-- The power of a canonical factor after its merges. -/
private theorem mergedPower_ok (ho : o.Total) {b : Term} (k : ℤ) (hb : Term.Canonical o me R b)
    (hf : b.factorOk = true) : OK (Term.Canonical o me R) (mergedPower o me b k) := by
  unfold mergedPower
  refine (mergePowers_ok b hb hf k).bind fun ⟨c, j⟩ ⟨hc, hcf, hcm⟩ => ?_
  dsimp only; split; · exact hc
  split; · exact canon_powerZero ho hc
  refine buildProduct_ok ho ⟨fun x hx => ?_, by simp⟩
  obtain rfl : x = _ := by simpa using hx
  refine ⟨hc, hcf, ?_, fun c' j' e => ?_⟩
  · cases e : c.isOne; · rfl
    obtain ⟨c', rfl⟩ := isOne_eq e
    exact absurd (mergeCondition_false.1 (hcm _ 0 rfl)).1 (lt_irrefl 0)
  · have := mergeCondition_false.1 (hcm c' j' e); exact ⟨this.1, by omega⟩

/-- A power of a canonical base that is no number, past the exponents 0 and 1. -/
private theorem distributedPower_ok (ho : o.Total) {b : Term} (k : ℤ)
    (hb : Term.Canonical o me R b) (hv : b.isCondition = false) (hn : ∀ r, b ≠ .number r) :
    OK (Term.Canonical o me R) (distributedPower o me b k) := by
  cases b with
  | product c fs =>
    have hf := factors_ok hb
    exact (ratPow_ok c k).bind fun ck _ => (OK.mapM fun f h => mergedPower_ok ho k (hf f h).1
      (hf f h).2).bind fun rs hrs => mkProduct_ok ho (by simpa using ⟨canonical_number ck, hrs⟩)
  | sum c ms =>
    exact (ratPow_ok _ k).bind fun ck _ => buildProduct_ok ho
      ⟨by simpa using ⟨(canon_prim hb).1, (canon_prim hb).2, rfl, nofun⟩, by simp⟩
  | number r => exact absurd rfl (hn r)
  | condition => simp [Term.isCondition] at hv
  | _ => exact mergedPower_ok ho k hb rfl

/-- A power of a canonical base. -/
private theorem mkPower_ok (ho : o.Total) {b : Term} (k : ℤ) (hb : Term.Canonical o me R b) :
    OK (Term.Canonical o me R) (mkPower o me b k) := by
  unfold mkPower; refine OK.check ?_
  split; · simp [OK]
  rename_i hv
  cases b with
  | number r =>
    by_cases h : r = 0 ∧ k < 0 <;> simp [Kalyx.Spec.Fields.ratPowOp, Kalyx.Spec.Fields.ratPow,
      Kalyx.Spec.Fields.FieldError.lift, h, OK, Result.ofOutcome, Result.map,
      TermFault.ofFieldError, canonical_number]
  | _ =>
    dsimp only; split; · exact hb
    split; · exact canon_powerZero ho hb
    exact distributedPower_ok ho k hb (by simpa using hv) nofun

/-- A symbol is canonical when its name has the form of a name and is not reserved. -/
private theorem canon_symbol {s : String} :
    Term.Canonical o me R (.symbol s) ↔ (nameFault s).isNone && !reservedNames.contains s := by
  rw [canon_iff, Term.nodes, List.forall_mem_singleton]; simp [NodeOk, Term.nodeOk]

/-- A call of canonical arguments: canonical values, and `Internal` only from the rules. -/
private theorem mkCall_ok (hR : R.Closed (fun me => Term.Canonical o me R) Term.negBases)
    {h : Head} {args : List Term} (ha : ∀ a ∈ args, Term.Canonical o me R a) :
    (∀ u, mkCall me R h args = .value u → Term.Canonical o me R u) ∧
      (mkCall me R h args = .fault .internal → R.apply me h args = .fault .internal) := by
  unfold mkCall; split; · simp
  rename_i hok; simp only [Bool.not_eq_true', Bool.not_eq_false] at hok
  split
  · rename_i t ht
    refine ⟨fun u hu => ?_, by simp⟩
    cases hu; split at ht; swap; · cases ht
    unfold piecewiseBranch at ht; split at ht; swap; · cases ht
    cases ht; split <;> exact ha _ (by simp)
  · rename_i hpb
    cases hr : R.apply me h args <;> dsimp only
    · refine ⟨fun u hu => ?_, by simp⟩; cases hu; refine canon_call.2 ⟨?_, ha⟩
      simp only [canonicalCall, hok, hr, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne,
        Option.isNone_iff_eq_none, beq_self_eq_true, and_true, true_and]
      by_cases hp : h = Head.piecewise
      · exact .inr (by simpa [hp] using hpb)
      · exact .inl hp
    · exact ⟨fun u hu => by cases hu; exact (hR me h args _ ha hr).1, by simp⟩
    · exact ⟨by simp, fun e => by cases e; rfl⟩
    · exact ⟨by simp, by simp⟩

/-! ## Results that only a check stops -/

/-- `r` is the value `v` when `ok` holds, and has no other value. -/
private def Lim (ok : Prop) (v : α) (r : Result α) : Prop := (ok → r = .value v) ∧ ∀ w, r = .value w → w = v

/-- `Lim` of a value. -/
private theorem Lim.val {p : Prop} {v : α} : Lim p v (.value v) :=
  ⟨fun _ => rfl, fun _ h => (Result.value.inj h).symm⟩

/-- `Lim` under a stronger condition, of an equal value. -/
private theorem Lim.mono {p q : Prop} {v w : α} {r : Result α} (h : Lim p v r) (hq : q → p) (e : v = w) :
    Lim q w r := e ▸ ⟨fun h' => h.1 (hq h'), h.2⟩

/-- `Lim` through a `bind`. -/
private theorem Lim.bind {p q : Prop} {v : α} {w : β} {x : Result α} {f : α → Result β} (hx : Lim p v x)
    (hf : Lim q w (f v)) : Lim (p ∧ q) w (x >>= f) :=
  ⟨fun h => by rw [hx.1 h.1]; exact hf.1 h.2, fun u h => by
    obtain ⟨a, ha, h⟩ := bind_eq_value.1 h; rw [hx.2 a ha] at h; exact hf.2 u h⟩

/-- `Lim` through a `bind` into a value. -/
private theorem Lim.bindPure {p : Prop} {v : α} {w : β} {x : Result α} {f : α → β} (hx : Lim p v x)
    (e : f v = w) : Lim p w (x >>= fun a => pure (f a)) :=
  (hx.bind (f := fun a => pure (f a)) Lim.val).mono (fun h => ⟨h, trivial⟩) e

/-- `Lim` through a check of an exponent. -/
private theorem Lim.check {p : Prop} {v : α} {k : ℤ} {n : Unit → Result α} (h : Lim p v (n ())) :
    Lim (k.natAbs ≤ exponentBound me ∧ p) v (checkExponent me k n) := by
  unfold checkExponent; split
  exacts [⟨fun h' => absurd h'.1 (by omega), fun _ e => by cases e⟩, ⟨fun h' => h.1 h'.2, h.2⟩]

/-- `Lim` through `mapM`. -/
private theorem Lim.mapM {f : α → Result β} {g : α → β} {p : α → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, Lim (p a) (g a) (f a)) → Lim (∀ a ∈ l, p a) (l.map g) (l.mapM f)
  | [], _ => by rw [List.mapM_nil]; exact Lim.val
  | a :: l, h => by
    rw [List.mapM_cons]
    exact ((h a (by simp)).bind (Lim.bindPure (Lim.mapM fun x hx => h x (.tail _ hx)) rfl)).mono
      (fun h' => ⟨h' a (by simp), fun x hx => h' x (.tail _ hx)⟩) rfl

/-! ## Rebuilding products -/

/-- The item of a factor: a power gives its base and exponent, any other factor itself and 1. -/
private def fItem : Term → Term × ℤ
  | .power b k => (b, k)
  | t => (t, 1)

/-- The parts of one factor: a one is set aside, any other factor gives its item. -/
private def onePart (f : Term) : ProductParts :=
  ⟨1, if f.isOne then [] else [fItem f], if f.isOne then [f] else []⟩

/-- The items of the factors that are no ones. -/
private abbrev fItems (fs : List Term) : List (Term × ℤ) := (fs.filter fun f => !f.isOne).map fItem

/-- The exponents of the items of factors pass the check. -/
private abbrev Bnd (me : ℕ) (fs : List Term) : Prop := ∀ f ∈ fs, (fItem f).2.natAbs ≤ exponentBound me

/-- The parts of factors appended to `p`. -/
private theorem foldl_onePart (fs : List Term) (p : ProductParts) : (fs.map onePart).foldl ProductParts.append p =
    ⟨p.coefficient, p.items ++ fItems fs, p.ones ++ fs.filter Term.isOne⟩ := by
  induction fs generalizing p with
  | nil => cases p; simp
  | cons f fs ih =>
    rw [List.map_cons, List.foldl_cons, ih]
    cases h : f.isOne <;> simp [ProductParts.append, onePart, h, fItems]

/-- The item of a canonical factor that is no one: settled, and it gives the factor and its key. -/
private theorem fItem_ok {f : Term} (hf : Term.Canonical o me R f) (h1 : f.isOne = false) :
    (fItem f).2 ≠ 0 ∧ ((fItem f).1 = Term.imaginaryUnit → (fItem f).2 = 1) ∧
      (∀ u n, rootOf (fItem f).1 = some (u, n) → (fItem f).2 < n) ∧ itemFactor (fItem f) = f ∧
      Key.of (fItem f).1 (fItem f).2 = f.key := by
  cases f with
  | power b k =>
    obtain ⟨-, h2, h3, h4, -, -⟩ := canonicalPower_iff.1 (canon_power.1 hf).1
    exact ⟨fun hk => (by rw [(power_isOne hf).2 hk] at h1; cases h1), fun e => absurd e h2, h4,
      by simp [itemFactor, fItem, h3], rfl⟩
  | _ => exact ⟨one_ne_zero, fun _ => rfl, fun u n h => by
      have := (rootOf_some h).1; simp only [fItem]; omega, by simp [itemFactor, fItem], rfl⟩

/-- A sum of content 1 is its own primitive part. -/
private theorem prim_self {c : ℚ} {ms : List (ℚ × Term)} (h : sumContent c ms = 1) : primitivePart c ms = .sum c ms :=
  by simp [primitivePart, scaleSum, h]

/-- The parts of a canonical factor. -/
private theorem itemParts_lim {f : Term} (hf : Term.Canonical o me R f) (hfo : f.factorOk = true) :
    Lim ((fItem f).2.natAbs ≤ exponentBound me) (onePart f) (itemParts me 1 f) := by
  cases f with
  | sum c ms =>
    have h1 : sumContent c ms = 1 := by simpa [Term.factorOk] using hfo
    exact Lim.val.mono id (by simp [onePart, prim_self h1, h1, Term.isOne, fItem])
  | power b j =>
    by_cases hj : j = 0
    · subst hj; simp [itemParts, onePart, (power_isOne hf).2 rfl]; exact Lim.val
    · simp only [itemParts, hj, ↓reduceIte, mul_one]
      exact Lim.mono (Lim.check Lim.val) (fun h => ⟨h, trivial⟩) (by simp [onePart, fItem, (power_not_one hj).1])
  | _ => exact Lim.val

/-- The parts of a number and canonical factors. -/
private theorem productParts_lim {a : ℚ} {fs : List Term}
    (hfs : ∀ f ∈ fs, Term.Canonical o me R f ∧ f.factorOk = true) :
    Lim (Bnd me fs) ⟨a, fItems fs, fs.filter Term.isOne⟩ (productParts me (.number a :: fs)) := by
  simp only [productParts, List.mapM_cons, factorParts, bind_value, bind_assoc, pure_bind]
  refine Lim.bindPure (Lim.mapM (g := onePart) fun f h => ?_)
    (by simp [foldl_onePart, ProductParts.unit, ProductParts.append])
  have := (hfs f h).2
  rw [show factorParts me 1 f = itemParts me 1 f by cases f <;> first | rfl | simp [Term.factorOk] at this]
  exact itemParts_lim (hfs f h).1 this

/-- The coefficient and the factors of a term read as a product. -/
private def asProduct : Term → ℚ × List Term
  | .number q => (q, [])
  | .product c fs => (c, fs)
  | .sum c ms => (sumContent c ms, [primitivePart c ms])
  | t => (1, [t])

/-- A canonical value read as a product: its factors, their keys, shape and assembly. -/
private theorem asProduct_ok {t : Term} (ht : Term.Canonical o me R t) (hv : t.isCondition = false) :
    (∀ f ∈ (asProduct t).2, Term.Canonical o me R f ∧ f.factorOk = true) ∧
      strictlyIncreasing (Key.cmp o) ((asProduct t).2.map Term.key) = true ∧
      ((asProduct t).1 = 0 → ∃ bs, (asProduct t).2.mapM Term.reciprocalBase? = some bs ∧ unnested bs = true) ∧
      ((asProduct t).1 ≠ 0 → onesOk (asProduct t).2 = true) ∧ t = assembleProduct (asProduct t).1 (asProduct t).2 := by
  cases t with
  | number q => exact ⟨by simp [asProduct], rfl, fun _ => ⟨[], rfl, rfl⟩, fun _ => rfl, rfl⟩
  | product c fs =>
    obtain ⟨hp, -⟩ := canon_product.1 ht
    refine ⟨factors_ok ht, by simp only [canonicalProduct, Bool.and_eq_true] at hp; exact hp.1.1.2,
      (onesOk_of hp).1, fun _ => (onesOk_of hp).2, ?_⟩
    rcases fs with _ | ⟨f, _ | ⟨g, fs⟩⟩
    · simp [canonicalProduct] at hp
    · simp only [canonicalProduct, Bool.and_eq_true] at hp
      have := hp.1.2; cases f <;> simp_all [assembleProduct, asProduct]
    · rfl
  | sum c ms =>
    have hne := sumContent_ne_zero (canon_sum.1 ht).1
    refine ⟨by simpa [asProduct] using canon_prim ht, rfl, fun h => absurd h hne, fun _ => onesOk_single _, ?_⟩
    by_cases h1 : sumContent c ms = 1
    · simp [asProduct, assembleProduct, h1, prim_self h1]
    · simp [asProduct, assembleProduct, h1, primitivePart, scaleSum, mul_inv_cancel_left₀ hne, Function.comp_def]
  | condition => simp [Term.isCondition] at hv
  | _ => exact ⟨by simpa [asProduct] using ⟨ht, rfl⟩, rfl, fun h => absurd h one_ne_zero, fun _ => onesOk_single _,
      by simp [asProduct, assembleProduct]⟩

/-- The rounds leave settled items with increasing keys as they are, once their exponents pass. -/
private theorem settle_fixed (ho : o.Total) {c : ℚ} {items : List (Term × ℤ)} {ones : List Term} (fuel : ℕ)
    (hs : ∀ x ∈ items, x.2 ≠ 0 ∧ (x.1 = Term.imaginaryUnit → x.2 = 1) ∧ ∀ u n, rootOf x.1 = some (u, n) → x.2 < n)
    (hk : strictlyIncreasing (Key.cmp o) (items.map fun x => Key.of x.1 x.2) = true) :
    Lim (∀ x ∈ items, x.2.natAbs ≤ exponentBound me) ⟨c, items, ones⟩
      (settleItems o me (fuel + 1) ⟨c, items, ones⟩) := by
  rw [settleItems]; dsimp only; rw [mergeItems_eq_self (keyCmp_total o ho) hk]
  refine ((Lim.mapM (g := fun x => ((⟨1, [x], []⟩ : ProductParts), ([] : List (Term × ℤ)))) fun x hx => ?_).bind
    ?_).mono (fun h => ⟨h, trivial⟩) rfl
  · obtain ⟨b, k⟩ := x; obtain ⟨h0, hi, hr⟩ := hs _ hx
    rw [reduceItem]; refine (Lim.check ?_).mono (fun h => ⟨h, trivial⟩) rfl
    dsimp only; rw [ite_eq_right h0]; split
    · obtain rfl := hi ‹_›; exact Lim.val.mono id (by simp)
    · rcases e : rootOf b with _ | ⟨u, n⟩
      · exact Lim.val
      · have h' : ¬ (n : ℤ) ≤ k := by have := hr u n e; omega
        dsimp only; rw [ite_eq_right h']; exact Lim.val
  · have e2 : (items.map fun x => ((⟨1, [x], []⟩ : ProductParts), ([] : List (Term × ℤ)))).foldl
        (fun (acc : ProductParts) r => acc.append r.1) ⟨c, [], ones⟩ = ⟨c, items, ones⟩ := by
      rw [← List.foldl_map (f := Prod.fst), foldl_append]; simp [Function.comp_def, ← List.flatMap_def, List.map_const']
    simp only [e2, List.map_map, Function.comp_def, List.map_const', List.flatten_replicate_nil, List.isEmpty_nil,
      ↓reduceIte]
    exact Lim.val

/-- Unnested bases with increasing reciprocal keys are the maximal elements of a list in their `N`. -/
private theorem maxBases_recips (ho : o.Total) {bs L : List Term} (hc : ∀ b ∈ bs, b.isConstant = false)
    (hu : unnested bs = true) (hk : strictlyIncreasing (Key.cmp o) ((bs.map Term.reciprocal).map Term.key) = true)
    (hb : ∀ b ∈ bs, b ∈ L) (hL : ∀ x ∈ L, x ∈ Term.negBasesList (bs.map Term.reciprocal)) : maxBases o L = bs := by
  have := (keyCmp_total o ho).1
  rw [List.map_map, strictlyIncreasing_iff_pairwise, List.pairwise_map] at hk
  have hs : bs.Pairwise fun a b => Term.cmp o a b = .lt := hk.imp_of_mem fun ha hb h => by
    simpa [Term.reciprocal, Term.key, Key.of, Key.cmp, hc _ ha, hc _ hb] using h
  refine maxBases_closure ho hs hu hb fun x hx => ?_
  obtain ⟨b, hb, h | h⟩ := (mem_negBases_reciprocals hc).1 (hL x hx)
  exacts [.inl (h ▸ hb), .inr ⟨b, hb, h⟩]

/-- The ones of factors are the ones of their bases. -/
private theorem filter_isOne : ∀ fs : List Term, fs.filter Term.isOne = (fs.filterMap Term.oneBase?).map Term.oneOf
  | [] => rfl
  | f :: fs => by
    cases h : f.isOne
    · simp [h, oneBase_none h, filter_isOne fs]
    · obtain ⟨b, rfl⟩ := isOne_eq h; simp [Term.oneOf, Term.oneBase?, Term.isOne, filter_isOne fs]

/-- `N` of a one over a base that is no constant. -/
private theorem mem_negBases_oneOf {b x : Term} (hb : b.isConstant = false) :
    x ∈ b.oneOf.negBases ↔ x = b ∨ x ∈ b.negBases := by simp [Term.oneOf, Term.negBases, hb]

/-- The rounds and the assembly of the parts of canonical factors give their product. -/
private theorem build_lim (ho : o.Total) {d : ℚ} {fs : List Term}
    (hfs : ∀ f ∈ fs, Term.Canonical o me R f ∧ f.factorOk = true)
    (hk : strictlyIncreasing (Key.cmp o) (fs.map Term.key) = true)
    (h0 : d = 0 → ∃ bs, fs.mapM Term.reciprocalBase? = some bs ∧ unnested bs = true) (h1 : d ≠ 0 → onesOk fs = true) :
    Lim (Bnd me fs) (assembleProduct d fs) (buildProduct o me ⟨d, fItems fs, fs.filter Term.isOne⟩) := by
  have hT := termCmp_total o ho; have hK := keyCmp_total o ho; have := hT.1; have := hK.1
  have hO : ∀ f ∈ fs.filter (fun f => !f.isOne), _ := fun f hf =>
    have := List.mem_filter.1 hf; fItem_ok (hfs f this.1).1 (by simpa using this.2)
  have hF : (fItems fs).map itemFactor = fs.filter fun f => !f.isOne := by
    rw [List.map_map]; exact (List.map_congr_left fun f hf => (hO f hf).2.2.2.1).trans (List.map_id _)
  have hkI : strictlyIncreasing (Key.cmp o) ((fItems fs).map fun x => Key.of x.1 x.2) = true := by
    simp only [List.map_map, Function.comp_def]
    rw [List.map_congr_left fun f hf => (hO f hf).2.2.2.2]; exact strictlyIncreasing_filter_map hk _
  rw [build_eq]
  refine (Lim.bindPure (settle_fixed ho _ (List.forall_mem_map.2 fun f hf => ⟨(hO f hf).1, (hO f hf).2.1,
    (hO f hf).2.2.1⟩) hkI) ?_).mono (fun h => List.forall_mem_map.2 fun f hf => h f (List.mem_filter.1 hf).1) rfl
  unfold Products.finish; dsimp only; rw [hF]; split
  · rename_i hd; obtain ⟨bs, hbs, hu⟩ := h0 hd; subst hd
    obtain ⟨rfl, hc⟩ := mapM_recip_eq hbs
    have hn : ∀ f ∈ bs.map Term.reciprocal, f.isOne = false := fun f hf => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hf; exact (power_not_one (by norm_num)).1
    rw [List.filter_eq_self.2 (by simpa using hn), List.filter_eq_nil_iff.2 (by simpa using hn), List.append_nil,
      maxBases_recips ho hc hu hk (fun b hb => (mem_negBases_reciprocals hc).2 ⟨b, hb, .inl rfl⟩) fun x hx => hx]
    rcases bs with _ | ⟨b, _ | ⟨b', bs⟩⟩ <;> simp [zeroWitness, assembleProduct, Term.reciprocal]
  · rename_i hd
    have hon := h1 hd
    obtain ⟨-, hheld⟩ := onesOk_iff.1 hon
    have hb : ∀ b ∈ fs.filterMap Term.oneBase?, b.isConstant = false := fun b hb => by
      obtain ⟨f, hf, e⟩ := List.mem_filterMap.1 hb; obtain rfl := oneBase_eq e
      obtain ⟨-, -, -, -, h5, -⟩ := canonicalPower_iff.1 (canon_power.1 (hfs _ hf).1).1
      exact ((h5 _ _ rfl).2.resolve_left (by simp)).2
    have hkept : maxBases o (uncovered (Term.negBasesList ((fs.filterMap Term.oneBase?).map Term.oneOf))
        (Term.negBasesList (fs.filter fun f => !f.isOne))) = fs.filterMap Term.oneBase? := by
      refine maxBases_closure ho (List.pairwise_filterMap.2 ((pairwise_of_strictlyIncreasing_map hk).imp
        fun {f g} h b hb b' hb' => ?_)) (unnested_iff.2 (onesOk_iff.1 hon).1) (fun b hb' => mem_uncovered.2
          ⟨mem_negBasesList.2 ⟨b.oneOf, List.mem_map_of_mem hb', (mem_negBases_oneOf (hb b hb')).2 (.inl rfl)⟩,
            fun h => ?_⟩) fun x hx => ?_
      · obtain rfl := oneBase_eq hb; obtain rfl := oneBase_eq hb'
        simpa [Term.oneOf, Term.key, Key.of, Key.cmp, cmp_power] using h
      · obtain ⟨f, hf, hbf⟩ := mem_negBasesList.1 h
        have := List.mem_filter.1 hf; exact hheld b hb' f this.1 (by simpa using this.2) hbf
      · obtain ⟨t, ht, hxt⟩ := mem_negBasesList.1 (mem_uncovered.1 hx).1
        obtain ⟨b, hb', rfl⟩ := List.mem_map.1 ht
        rcases (mem_negBases_oneOf (hb b hb')).1 hxt with rfl | h
        exacts [.inl hb', .inr ⟨b, hb', h⟩]
    have hp : (fs.filter (fun f => !f.isOne) ++ fs.filter Term.isOne).Perm fs := by
      simpa using List.filter_append_perm (fun f : Term => !f.isOne) fs
    rw [filter_isOne, hkept, ← filter_isOne, eq_of_strictlyIncreasing_map Term.key (strictlyIncreasing_sortBy_map hK
      Term.key ((hp.map _).nodup_iff.2 (nodup_of_pairwise_lt (strictlyIncreasing_iff_pairwise.1 hk)))) hk
      fun x => (perm_sortBy _ _).mem_iff.trans hp.mem_iff]

/-- The product of a number and a canonical value, read as a product. -/
private theorem mk_lim (ho : o.Total) (a : ℚ) {t : Term} (ht : Term.Canonical o me R t) (hv : t.isCondition = false)
    (hz : a * (asProduct t).1 = 0 → ∃ bs, (asProduct t).2.mapM Term.reciprocalBase? = some bs ∧ unnested bs = true) :
    Lim (Bnd me (asProduct t).2) (assembleProduct (a * (asProduct t).1) (asProduct t).2)
      (mkProduct o me [.number a, t]) := by
  obtain ⟨hfs, hk, -, h1, -⟩ := asProduct_ok ht hv
  have hn : ¬ ([Term.number a, t].any Term.isCondition = true) := by
    simp [hv, show (Term.number a).isCondition = false from rfl]
  unfold mkProduct; rw [ite_eq_right hn]
  refine ((?_ : Lim (Bnd me (asProduct t).2) ⟨a * (asProduct t).1, fItems (asProduct t).2,
    (asProduct t).2.filter Term.isOne⟩ (productParts me [.number a, t])).bind
      (build_lim ho hfs hk hz fun h => h1 (right_ne_zero_of_mul h))).mono (fun h => ⟨h, h⟩) rfl
  cases t with
  | number q => exact Lim.val.mono id (by simp [ProductParts.unit, ProductParts.append, asProduct])
  | sum c ms => exact Lim.val.mono id (by simp [ProductParts.unit, ProductParts.append, asProduct,
      primitivePart, scaleSum, Term.isOne, fItems, fItem])
  | product c fs =>
    simp only [productParts, List.mapM_cons, List.mapM_nil, factorParts, bind_value, bind_assoc, pure_bind]
    exact Lim.bindPure (Lim.mapM (g := onePart) fun f h => itemParts_lim (hfs f h).1 (hfs f h).2)
      (by simp [foldl_onePart, ProductParts.unit, ProductParts.append, asProduct])
  | condition => simp [Term.isCondition] at hv
  | _ => exact (productParts_lim hfs).mono id (by simp [asProduct])

/-- A product of factors reads in a sum as the coefficient times the product of coefficient 1. -/
private theorem sumParts_assemble (d : ℚ) {fs : List Term} (h : ∀ f ∈ fs, f.factorOk = true) :
    sumParts [assembleProduct d fs] = (d * (sumParts [assembleProduct 1 fs]).1,
      (sumParts [assembleProduct 1 fs]).2.map fun m => (d * m.1, m.2)) := by
  rcases fs with _ | ⟨f, _ | ⟨g, fs⟩⟩
  · simp [assembleProduct, sumParts]
  · have := h f (by simp)
    by_cases d1 : d = 1
    · subst d1; simp
    · cases f <;> simp_all [assembleProduct, sumParts, scaleSum, Term.factorOk, productCore]
  · simp [assembleProduct, sumParts]

/-- The coefficients of scaled monomials. -/
private theorem coefficientOf_map (d : ℚ) (s : Term) (ms : List (ℚ × Term)) :
    coefficientOf s (ms.map fun m => (d * m.1, m.2)) = d * coefficientOf s ms := by
  simp [coefficientOf, List.filter_map, Function.comp_def, List.sum_map_mul_left]

/-- Proves `NegationReadsOpposite`: the negation of a canonical term reads in a sum with the
opposite constant and coefficients. -/
public theorem negationReadsOpposite : Bases.NegationReadsOpposite := by
  intro o me R ho t nb ht h
  cases hv : t.isCondition
  · obtain ⟨hfs, -, h0, -, he⟩ := asProduct_ok ht hv
    rw [(mk_lim ho (-1) ht hv fun e => h0 (by simpa using e)).2 nb h]
    generalize asProduct t = p at hfs he ⊢
    subst he
    rw [sumParts_assemble (-1 * p.1) fun f hf => (hfs f hf).2, sumParts_assemble p.1 fun f hf => (hfs f hf).2]
    simp only [coefficientOf_map]; exact ⟨by ring, fun s => by ring⟩
  · simp [mkNegate, mkProduct, hv] at h

/-! ## Rebuilding -/

/-- Under a positive limit, the exponents that a term allows pass the checks of its factors. -/
private theorem bnd_of {t : Term} {fs : List Term} (h1 : 0 < me) (hw : t.exponentsWithin me = true)
    (hfs : ∀ f ∈ fs, f ∈ t.nodes) : Bnd me fs := fun f hf => by
  have := List.all_eq_true.1 hw f (hfs f hf)
  by_cases hp : ∃ b k, f = .power b k
  · obtain ⟨b, k, rfl⟩ := hp; simpa [fItem] using this
  · rw [show fItem f = (f, 1) by cases f <;> simp_all [fItem]]; simp [exponentBound]; omega

/-- The read of a core as a product. -/
private theorem asProduct_core {t : Term} (h : t.coreOk = true) : asProduct t = (1, t.coreFactors) := by
  cases t <;> simp_all [Term.coreOk, asProduct, Term.coreFactors]

/-- The bases of a witness core: the core is the product of their reciprocals. -/
private theorem witnessBases_eq {w : Term} {bs : List Term} (h : witnessBases? w = some bs) :
    w.coreFactors = bs.map Term.reciprocal ∧ ∀ b ∈ bs, b.isConstant = false := by
  unfold witnessBases? at h; split at h
  · split_ifs at h; exact mapM_recip_eq h
  · obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, hc⟩ := recipBase_eq hb
    exact ⟨rfl, by simpa using hc⟩

/-- A canonical sum is its own cancellation; a monomial of coefficient 0 is the witness. -/
private theorem cancel_fixed (ho : o.Total) {c : ℚ} {ms : List (ℚ × Term)} (hcs : canonicalSum o c ms = true)
    (hms : ∀ m ∈ ms, Term.Canonical o me R m.2) (hCS : ∀ m ∈ ms, Sums.CoreShape m.2) :
    (∀ m ∈ ms, m.1 = 0 → ∃ bs, witnessBases? m.2 = some bs ∧ unnested bs = true) ∧ cancelMonomials o ms = ms := by
  have hT := termCmp_total o ho; have := hT.1
  have h := hcs; simp only [canonicalSum, Bool.and_eq_true] at h
  obtain ⟨⟨-, hs⟩, hz⟩ := h
  have hp : ((ms.filter fun m => decide (m.1 = 0)) ++ ms.filter fun m => decide (m.1 ≠ 0)).Perm ms := by
    simpa using List.filter_append_perm (fun m : ℚ × Term => decide (m.1 = 0)) ms
  have hZ : ∀ m ∈ ms, m.1 = 0 → m ∈ ms.filter fun m => decide (m.1 = 0) :=
    fun m hm h0 => List.mem_filter.2 ⟨hm, by simpa using h0⟩
  rw [Sums.cancelMonomials_eq, Sums.cancelBases]
  generalize hZ' : ms.filter (fun m => decide (m.1 = 0)) = Z at hz hp hZ
  rcases Z with _ | ⟨⟨x, w⟩, _ | ⟨_, _⟩⟩
  · have h0 : ∀ m ∈ ms, m.1 ≠ 0 := fun m hm e => by simpa using hZ m hm e
    exact ⟨fun m hm e => absurd e (h0 m hm), by simpa [Term.negBasesPairs, uncovered, maxBases_eq_nil] using h0⟩
  · obtain ⟨hxm, hx0⟩ := List.mem_filter.1 (hZ' ▸ List.mem_singleton_self _ : (x, w) ∈ ms.filter _)
    obtain rfl : x = 0 := by simpa using hx0
    dsimp only at hz; split at hz; swap; · cases hz
    rename_i bs hbs
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hz
    obtain ⟨hu, hheld⟩ := hz
    refine ⟨fun m hm e => ?_, ?_⟩
    · obtain rfl : m = (0, w) := by simpa using hZ m hm e
      exact ⟨bs, hbs, hu⟩
    obtain ⟨hcf, hc⟩ := witnessBases_eq hbs
    have hk := (asProduct_ok (hms _ hxm) (coreOk_value (hCS _ hxm).1)).2.1
    rw [asProduct_core (hCS _ hxm).1, hcf] at hk
    have hwc : w = witnessCore bs := by
      have e : productCore w.coreFactors = w := (hCS _ hxm).2
      rw [hcf] at e; rw [← e]; rcases bs with _ | ⟨b, _ | ⟨b', bs⟩⟩ <;> rfl
    have hne : bs ≠ [] := by
      rintro rfl; have := hms _ hxm; rw [hwc] at this; simp [witnessCore, canon_product, canonicalProduct] at this
    have hN : ∀ x, x ∈ Term.negBasesPairs [(0, w)] ↔ x ∈ Term.negBasesList (bs.map Term.reciprocal) :=
      fun x => by rw [← hcf, ← negBases_coreFactors]; simp [Term.negBasesPairs]
    have hB : maxBases o (uncovered (Term.negBasesPairs [(0, w)])
        (Term.negBasesPairs (ms.filter fun m => decide (m.1 ≠ 0)))) = bs :=
      maxBases_recips ho hc hu hk (fun b hb => mem_uncovered.2 ⟨(hN b).2
        ((mem_negBases_reciprocals hc).2 ⟨b, hb, .inl rfl⟩), hheld b hb⟩) fun y hy => (hN y).1 (mem_uncovered.1 hy).1
    have hnd := (hp.map Prod.snd).nodup_iff.2 (nodup_of_pairwise_lt (strictlyIncreasing_iff_pairwise.1 hs))
    rw [hB, ite_eq_right hne, ← hwc]
    exact eq_of_strictlyIncreasing_map Prod.snd (strictlyIncreasing_insertBy_map hT Prod.snd
      (strictlyIncreasing_filter_map hs _) (List.nodup_cons.1 hnd).1) hs
        fun m => (perm_insertBy _ _ _).mem_iff.trans hp.mem_iff
  · simp at hz

/-- Terms that read back as single monomials read back as the monomials. -/
private theorem sumParts_map {F : ℚ × Term → Term} : ∀ {ms : List (ℚ × Term)},
    (∀ m ∈ ms, sumParts [F m] = (0, [m])) → sumParts (ms.map F) = (0, ms)
  | [], _ => rfl
  | m :: ms, h => by
    rw [List.map_cons, show ∀ (u : Term) us, u :: us = [u] ++ us from fun _ _ => rfl, Sums.sumParts_append,
      h m (by simp), sumParts_map fun m hm => h m (.tail _ hm)]
    simp

/-- A canonical term is rebuilt into itself under a positive limit that allows its exponents. -/
private theorem rebuild_eq (ho : o.Total) (h1 : 0 < me) {t : Term} (ht : Term.Canonical o me R t)
    (hw : t.exponentsWithin me = true) : t.rebuild o me R = .value t := by
  cases t with
  | number => rfl
  | constant c =>
    have := (canon_iff.1 ht _ (mem_nodes_self _)).1
    simp [Term.nodeOk, Constant.hasClosedForm] at this; simp [Term.rebuild, this]
  | symbol s => have := canon_symbol.1 ht; simp at this; simp [Term.rebuild, mkSymbol, this]
  | call h args =>
    have hc := (canon_call.1 ht).1
    simp only [canonicalCall, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, Option.isNone_iff_eq_none,
      beq_iff_eq] at hc
    simp [Term.rebuild, mkCall, hc.1.1, hc.2, show (if h = Head.piecewise then piecewiseBranch args else none) =
      none by split <;> simp_all]
  | condition s ops => simp [Term.rebuild, (canon_condition.1 ht).1]
  | power b k =>
    obtain ⟨hcp, -⟩ := canon_power.1 ht
    obtain ⟨hf, -, h1k, -, h5, h6⟩ := canonicalPower_iff.1 hcp
    have hB : Bnd me [.power b k] := bnd_of h1 hw (by simp [mem_nodes_self])
    have hk' : ¬ exponentBound me < k.natAbs := by simpa [fItem] using hB (.power b k) (by simp)
    simp only [Term.rebuild, mkPower, checkExponent, hk', factorOk_value hf, Bool.false_eq_true, ↓reduceIte]
    by_cases k0 : k = 0
    · subst k0; cases b with
      | power c j =>
        obtain ⟨-, h | ⟨rfl, hc⟩⟩ := (h5 c j rfl); · exact absurd rfl h
        have : maxBases o (Term.power c (-1)).negBases = [c] := maxBases_recips ho (by simpa)
          (by simp [unnested, not_mem_self]) rfl (by simp [Term.negBases, hc])
            fun x hx => by simpa [Term.negBasesList, Term.reciprocal] using hx
        simp [powerZero, this, Term.oneOf]
      | _ => exact absurd rfl (h6 nofun)
    · have hP : buildProduct o me ⟨1, [(b, k)], []⟩ = .value (.power b k) := by
        have := (build_lim ho (d := 1) (fs := [.power b k]) (by simpa using ⟨ht, rfl⟩) rfl
          (fun h => absurd h one_ne_zero) fun _ => onesOk_single _).1 hB
        simpa [fItems, fItem, (power_not_one k0).1, assembleProduct] using this
      cases b with
      | number | product | condition => simp [Term.factorOk] at hf
      | sum c ms =>
        have hc : sumContent c ms = 1 := by simpa [Term.factorOk] using hf
        simp [distributedPower, Kalyx.Spec.Fields.ratPowOp, Kalyx.Spec.Fields.ratPow,
          Kalyx.Spec.Fields.FieldError.lift, Result.ofOutcome, hc, prim_self hc, h1k, k0, hP]
      | power c j => simp [distributedPower, mergedPower, mergePowers, (h5 c j rfl).1, h1k, k0, hP]
      | _ => simp [distributedPower, mergedPower, mergePowers, h1k, k0, hP]
  | product c fs =>
    obtain ⟨hfs, hk, h0, h1', he⟩ := asProduct_ok ht rfl
    dsimp only [asProduct] at hfs hk h0 h1' he
    have hB : Bnd me fs := bnd_of h1 hw fun f hf => coreFactors_nodes (t := .product c fs) hf
    have hn : ¬ ((Term.number c :: fs).any Term.isCondition = true) := by
      simpa [show (Term.number c).isCondition = false from rfl] using fun f hf => factorOk_value (hfs f hf).2
    simp only [Term.rebuild, mkProduct]
    rw [ite_eq_right hn, ((productParts_lim hfs).bind (build_lim ho hfs hk h0 h1')).1 ⟨hB, hB⟩, ← he]
  | sum c ms =>
    obtain ⟨hcs, hms⟩ := canon_sum.1 ht
    have hCS : ∀ m ∈ ms, Sums.CoreShape m.2 := fun m hm => Sums.coreShape_sumParts (ts := [.sum c ms])
      (by simpa using ht) (by simp [Term.isCondition]) m (by simpa [sumParts] using hm)
    obtain ⟨hW, hfix⟩ := cancel_fixed ho hcs hms hCS
    have hmono : ∀ m ∈ ms, Lim (Bnd me m.2.coreFactors) (assembleProduct m.1 m.2.coreFactors)
        (mkProduct o me [.number m.1, m.2]) ∧ sumParts [assembleProduct m.1 m.2.coreFactors] = (0, [m]) :=
      fun ⟨a, t⟩ hm => by
        have hc := (hCS _ hm).1
        have h := asProduct_ok (hms _ hm) (coreOk_value hc)
        have hl := mk_lim ho a (hms _ hm) (coreOk_value hc) fun h0 => by
          rw [asProduct_core hc] at h0 ⊢
          obtain ⟨bs, hbs, hu⟩ := hW _ hm (by simpa using h0)
          obtain ⟨hcf, hb⟩ := witnessBases_eq hbs
          exact ⟨bs, hcf ▸ mapM_recip hb, hu⟩
        simp only [asProduct_core hc, mul_one] at h hl
        have e := Sums.sumParts_assembleSum 0 (ms := [(1, t)]) (by simpa using hCS _ hm)
        simp only [assembleSum, ↓reduceIte] at e
        refine ⟨hl, ?_⟩
        rw [sumParts_assemble a fun f hf => (h.1 f hf).2, ← h.2.2.2.2, e]; simp
    simp only [Term.rebuild]
    rw [(Lim.mapM fun m hm => (hmono m hm).1).1 fun m hm => bnd_of h1 hw fun f hf => nodes_trans
      (List.mem_cons_of_mem _ (mem_nodesPairs.2 ⟨m, hm, mem_nodes_self _⟩)) (coreFactors_nodes hf)]
    simp only [bind_value]
    refine Sums.mkSum_eq_value.2 ⟨?_, ?_⟩
    · simp only [List.mem_cons, List.mem_map]
      rintro _ (rfl | ⟨m, hm', rfl⟩); · rfl
      have e := (hmono m hm').2; have hc := coreOk_value (hCS _ hm').1
      cases h : assembleProduct m.1 m.2.coreFactors <;> try rfl
      rw [h] at e; simp [sumParts] at e; subst e; simp [Term.isCondition] at hc
    · simp only [sumParts, sumParts_map fun m hm' => (hmono m hm').2, add_zero]
      simp only [canonicalSum, Bool.and_eq_true] at hcs
      rw [mergeMonomials_eq_self (termCmp_total o ho) hcs.1.2, hfix]
      have := hcs.1.1.1
      rcases ms with _ | ⟨⟨a, t⟩, _ | ⟨n, ms⟩⟩ <;> split_ifs at this <;> simp_all [assembleSum]

/-! ## The statements -/

/-- `OK` of the canonical form is a canonical result. -/
private theorem OK.canon {r : Result Term} (h : OK (Term.Canonical o me R) r) :
    CanonicalResult (Term.Canonical o me R) r := by cases r <;> exact h

/-- Proves `CanonicalFormsAreClosedAndIdempotent`: the constructors keep the canonical form, and a
canonical term is rebuilt into itself under a positive limit that allows its exponents. -/
public theorem canonicalFormsAreClosedAndIdempotent_holds : CanonicalFormsAreClosedAndIdempotent := by
  intro o me R ho hR
  have neg : ∀ t, Term.Canonical o me R t → OK (Term.Canonical o me R) (mkNegate o me t) :=
    fun t ht => mkProduct_ok ho (by simpa using ⟨canonical_number _, ht⟩)
  refine ⟨fun _ h => (mkSum_ok ho h).canon, fun _ h => (mkProduct_ok ho h).canon,
    fun _ k hb => (mkPower_ok ho k hb).canon, fun t ht => (neg t ht).canon,
    fun a b ha hb => ((neg b hb).bind fun nb hnb => mkSum_ok ho (by simpa using ⟨ha, hnb⟩)).canon,
    fun a b ha hb => ((mkPower_ok ho (-1) hb).bind fun r hr => mkProduct_ok ho (by simpa using ⟨ha, hr⟩)).canon,
    fun s ops h => ?_, fun name => ?_, fun _ _ ha => mkCall_ok hR ha, fun t ht h1 hw => rebuild_eq ho h1 ht hw⟩
  · unfold mkCondition; split; exacts [canon_condition.2 ⟨‹_›, h⟩, nofun]
  · unfold mkSymbol; split; · exact nofun
    split; exacts [nofun, canon_symbol.2 (by simp_all)]

end Kalyx.Proofs.Terms.Closure
