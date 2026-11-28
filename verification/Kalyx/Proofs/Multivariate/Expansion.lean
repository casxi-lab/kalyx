module

public import Kalyx.Proofs.Multivariate.Arithmetic
public import Kalyx.Proofs.Multivariate.Canonical
public import Kalyx.Proofs.Fields
public import Kalyx.Proofs.Terms.Basics
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# The expansion of terms into multivariate polynomials and its meaning

An unregistered helper module of the proofs about the multivariate
polynomials; it proves no registered statement. It holds, for the rings over
`ℚ`:

* the rationals as an exact coefficient ring (`rationalRing_exact`) and the
  fractions of rationals (`ofRat_reduced`, `ofRat_interpret`);
* the variable of a name (`variableName_of_variableIndex`,
  `variableIndex_isSome`), which is the variable of that name when the names
  are distinct (`variableIndex_variableName`);
* the meaning of the expansion: when the expansion of any term returns a
  polynomial, the polynomial is canonical and the term is defined at every
  assignment, under every interpretation, with its value (`expand_denote`), by
  induction over the term, the factors of a product and the monomials of a
  sum, since the ring operations return canonical polynomials that denote
  their results (`ringOperationsAreExact`);
* the expansion of a term whose nodes are numbers, powers, products, sums and
  the symbols of the variables, without a negative power, returns a polynomial
  (`expand_isValue`);
* when the names of the variables are distinct, two canonical polynomials with
  the same value at every assignment are equal (`eq_of_polyValue_eq`), since a
  polynomial over `ℚ` is determined by its values in `ℂ`.
-/

namespace Kalyx.Proofs.Multivariate.Expansion

open Kalyx.Spec.Fields Kalyx.Spec.Multivariate Kalyx.Statements.Multivariate MvPolynomial
open Kalyx.Spec.Terms (Term Interp Assignment zpowMeaning)
open Kalyx.Proofs.Terms (NodesFrom mem_nodes_self mem_nodes_factor mem_nodesPairs
  mem_negBasesList mem_negBasesPairs)

/-! ## The rationals -/

/-- The fraction of a rational number is reduced. -/
public theorem ofRat_reduced (q : ℚ) : (Fraction.ofRat q).Reduced := by
  refine ⟨Int.natCast_pos.mpr q.pos, ?_⟩
  show Nat.gcd q.num.natAbs (q.den : ℤ).natAbs = 1
  rw [Int.natAbs_natCast]
  exact q.reduced

/-- The fraction of a rational number denotes it. -/
public theorem ofRat_interpret (q : ℚ) : (Fraction.ofRat q).interpret = q := by
  simp [Fraction.ofRat, Fraction.interpret, Rat.num_div_den]

/-- The rationals are an exact coefficient ring. -/
public theorem rationalRing_exact : ExactRing rationalRing Rationals.model :=
  ⟨Kalyx.Proofs.Fields.ringAxioms.1, Kalyx.Proofs.Fields.zeroTestsAreExact.1⟩

/-- A `bind` of results that returns a value: the first result is a value. -/
public theorem mvBind_eq_value {α β : Type} {x : MvResult α} {f : α → MvResult β} {v : β} :
    x.bind f = .value v ↔ ∃ a, x = .value a ∧ f a = .value v := by
  cases x <;> simp [MvResult.bind]

/-! ## Variables by name -/

variable {n : ℕ} (r : MultivariateRing Rationals n)

/-- The position of a name is that of a variable with this name. -/
public theorem variableName_of_variableIndex {s : String} {i : Fin n}
    (h : r.variableIndex s = some i) : r.variableName i = s := by
  unfold MultivariateRing.variableIndex at h
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 h
  simpa [MultivariateRing.variableName] using (List.finIdxOf?_eq_some_iff.1 hj).1

/-- A name of a variable has a position. -/
public theorem variableIndex_isSome {s : String} (h : s ∈ r.variableNames) :
    ∃ i, r.variableIndex s = some i := by
  unfold MultivariateRing.variableIndex
  cases hj : r.variableNames.finIdxOf? s with
  | none => exact absurd h (List.finIdxOf?_eq_none_iff.1 hj)
  | some j => exact ⟨_, rfl⟩

/-- When the names are distinct, the position of the name of a variable is
its position. -/
public theorem variableIndex_variableName (hnd : r.variableNames.Nodup) (i : Fin n) :
    r.variableIndex (r.variableName i) = some i := by
  obtain ⟨j, hj⟩ := variableIndex_isSome r (s := r.variableName i)
    (by simp [MultivariateRing.variableName])
  rw [hj]
  have h := variableName_of_variableIndex r hj
  simp only [MultivariateRing.variableName] at h
  have := congrArg Fin.val (hnd.get_inj_iff.1 h)
  simp only [Fin.val_cast] at this
  exact congrArg some (Fin.ext this)

/-! ## The ring operations -/

/-- The canonical polynomials of the ring `r`. -/
private abbrev Canon (a : MvPoly n Fraction) : Prop :=
  a.Canonical Rationals.model r.coefficients r.order

/-- What the expansion uses of the ring operations of a ring over `ℚ`. -/
private theorem ops :
    (∀ i, r.Yields Rationals.model (r.generator rationalRing i) (X i)) ∧
    (∀ q : ℚ, r.Yields Rationals.model (r.constant rationalRing (Fraction.ofRat q)) (C q)) ∧
    (∀ a, Canon r a → ∀ k, r.Yields Rationals.model (r.power rationalRing a k)
      (a.interpret Rationals.model r.coefficients ^ k)) ∧
    ∀ a b, Canon r a → Canon r b →
      r.Yields Rationals.model (r.add rationalRing a b)
        (a.interpret Rationals.model r.coefficients + b.interpret Rationals.model r.coefficients) ∧
      r.Yields Rationals.model (r.multiply rationalRing a b)
        (a.interpret Rationals.model r.coefficients *
          b.interpret Rationals.model r.coefficients) := by
  obtain ⟨-, -, -, -, -, hg, hc, hp, ha, -, -⟩ :=
    Kalyx.Proofs.Multivariate.ringOperationsAreExact Rationals Fraction (fun _ => ℚ) rationalRing
      Rationals.model rationalRing_exact n r
  refine ⟨hg, fun q => ?_, fun a h k => (hp a h).2 k,
    fun a b h h' => ⟨(ha a b h h').1, (ha a b h h').2.2⟩⟩
  have := hc _ (ofRat_reduced q)
  simp only [Rationals.model, ofRat_interpret] at this
  exact this

/-- A value of a result that yields a polynomial is canonical and denotes it. -/
private theorem of_yields {o : MvResult (MvPoly n Fraction)} {x : MvPolynomial (Fin n) ℚ}
    {a : MvPoly n Fraction} (h : r.Yields Rationals.model o x) (ho : o = .value a) :
    Canon r a ∧ a.interpret Rationals.model r.coefficients = x := by
  obtain ⟨b, rfl, hb, hbx⟩ := h
  cases ho
  exact ⟨hb, hbx⟩

/-! ## The meaning of the expansion -/

section Expand

variable (I : Interp)

/-- A node expands into a canonical polynomial with its value, whenever it expands. -/
private abbrev Expands (t : Term) : Prop :=
  ∀ a, r.expand t = .value a → Canon r a ∧ ∀ ρ, t.denote I ρ = some (polyValue r a ρ)

/-- The factors of a product, multiplied into a canonical total. -/
private theorem expandFactors_spec :
    ∀ (fs : List Term) (total a : MvPoly n Fraction), (∀ f ∈ fs, Expands r I f) → Canon r total →
      MultivariateRing.expandFactors r total fs = .value a →
      Canon r a ∧ ∀ ρ, ∃ vs, Term.denoteList I ρ fs = some vs ∧
        polyValue r a ρ = polyValue r total ρ * vs.prod := by
  intro fs
  induction fs with
  | nil =>
    intro total a _ htc h
    simp only [MultivariateRing.expandFactors, MvResult.value.injEq] at h
    subst h
    exact ⟨htc, fun ρ => ⟨[], by simp [Term.denoteList]⟩⟩
  | cons f fs ih =>
    intro total a hfs htc h
    simp only [MultivariateRing.expandFactors, Canonical.bind_eq_bind] at h
    obtain ⟨g, hg, h⟩ := mvBind_eq_value.1 h
    obtain ⟨t, ht, h⟩ := mvBind_eq_value.1 h
    obtain ⟨hgc, hgd⟩ := hfs f List.mem_cons_self g hg
    obtain ⟨htc', hti⟩ := of_yields r ((ops r).2.2.2 total g htc hgc).2 ht
    obtain ⟨hac, had⟩ := ih t a (fun f' hf' => hfs f' (List.mem_cons_of_mem _ hf')) htc' h
    refine ⟨hac, fun ρ => ?_⟩
    obtain ⟨vs, hvs, hav⟩ := had ρ
    refine ⟨polyValue r g ρ :: vs, by simp [Term.denoteList, hgd ρ, hvs], ?_⟩
    rw [hav]
    simp only [polyValue, hti, eval₂_mul, List.prod_cons, mul_assoc]

/-- The monomials of a sum, each scaled and added to a canonical total. -/
private theorem expandMonomials_spec :
    ∀ (ms : List (ℚ × Term)) (total a : MvPoly n Fraction), (∀ m ∈ ms, Expands r I m.2) →
      Canon r total → MultivariateRing.expandMonomials r total ms = .value a →
      Canon r a ∧ ∀ ρ, ∃ v, Term.denotePairs I ρ ms = some v ∧
        polyValue r a ρ = polyValue r total ρ + v := by
  intro ms
  induction ms with
  | nil =>
    intro total a _ htc h
    simp only [MultivariateRing.expandMonomials, MvResult.value.injEq] at h
    subst h
    exact ⟨htc, fun ρ => ⟨0, by simp [Term.denotePairs]⟩⟩
  | cons m ms ih =>
    intro total a hms htc h
    obtain ⟨q, t⟩ := m
    simp only [MultivariateRing.expandMonomials, Canonical.bind_eq_bind] at h
    obtain ⟨g, hg, h⟩ := mvBind_eq_value.1 h
    obtain ⟨c, hc, h⟩ := mvBind_eq_value.1 h
    obtain ⟨s, hs, h⟩ := mvBind_eq_value.1 h
    obtain ⟨t', ht', h⟩ := mvBind_eq_value.1 h
    obtain ⟨hgc, hgd⟩ := hms (q, t) List.mem_cons_self g hg
    obtain ⟨hcc, hci⟩ := of_yields r ((ops r).2.1 q) hc
    obtain ⟨hsc, hsi⟩ := of_yields r ((ops r).2.2.2 g c hgc hcc).2 hs
    obtain ⟨ht'c, ht'i⟩ := of_yields r ((ops r).2.2.2 total s htc hsc).1 ht'
    obtain ⟨hac, had⟩ := ih t' a (fun m' hm' => hms m' (List.mem_cons_of_mem _ hm')) ht'c h
    refine ⟨hac, fun ρ => ?_⟩
    obtain ⟨v, hv, hav⟩ := had ρ
    refine ⟨q * polyValue r g ρ + v, by simp [Term.denotePairs, hgd ρ, hv], ?_⟩
    rw [hav]
    simp only [polyValue, ht'i, hsi, hci, eval₂_add, eval₂_mul, eval₂_C, eq_ratCast]
    ring

/-- Every node expands into a canonical polynomial with its value. -/
private theorem expand_spec : ∀ t, Expands r I t := by
  refine Kalyx.Proofs.Terms.term_induct (fun q => ?_) (fun c => ?_) (fun s => ?_)
    (fun hd args _ => ?_) (fun b k ih => ?_) (fun c fs ih => ?_) (fun c ms ih => ?_)
    (fun s os _ => ?_)
  · intro a h
    simp only [MultivariateRing.expand] at h
    obtain ⟨hac, hai⟩ := of_yields r ((ops r).2.1 q) h
    exact ⟨hac, fun ρ => by simp [Term.denote, polyValue, hai]⟩
  · intro a h
    simp [MultivariateRing.expand] at h
  · intro a h
    simp only [MultivariateRing.expand] at h
    split at h
    · rename_i i hs
      obtain ⟨hac, hai⟩ := of_yields r ((ops r).1 i) h
      exact ⟨hac, fun ρ => by simp [Term.denote, polyValue, hai,
        variableName_of_variableIndex r hs]⟩
    · cases h
  · intro a h
    simp [MultivariateRing.expand] at h
  · intro a h
    simp only [MultivariateRing.expand, Canonical.bind_eq_bind] at h
    obtain ⟨g, hg, h⟩ := mvBind_eq_value.1 h
    split at h
    · cases h
    · rename_i hk
      obtain ⟨hgc, hgd⟩ := ih g hg
      obtain ⟨hac, hai⟩ := of_yields r ((ops r).2.2.1 g hgc k.toNat) h
      refine ⟨hac, fun ρ => ?_⟩
      simp only [Term.denote, hgd ρ, Option.bind_some, zpowMeaning, hk, and_false, ↓reduceIte]
      rw [← Int.toNat_of_nonneg (not_lt.1 hk), zpow_natCast]
      simp only [polyValue, hai, eval₂_pow]
  · intro a h
    simp only [MultivariateRing.expand, Canonical.bind_eq_bind] at h
    obtain ⟨t, ht, h⟩ := mvBind_eq_value.1 h
    obtain ⟨htc, hti⟩ := of_yields r ((ops r).2.1 c) ht
    obtain ⟨hac, had⟩ := expandFactors_spec r I fs t a ih htc h
    refine ⟨hac, fun ρ => ?_⟩
    obtain ⟨vs, hvs, hav⟩ := had ρ
    rw [hav]
    simp [Term.denote, hvs, polyValue, hti]
  · intro a h
    simp only [MultivariateRing.expand, Canonical.bind_eq_bind] at h
    obtain ⟨t, ht, h⟩ := mvBind_eq_value.1 h
    obtain ⟨htc, hti⟩ := of_yields r ((ops r).2.1 c) ht
    obtain ⟨hac, had⟩ := expandMonomials_spec r I ms t a ih htc h
    refine ⟨hac, fun ρ => ?_⟩
    obtain ⟨v, hv, hav⟩ := had ρ
    rw [hav]
    simp [Term.denote, hv, polyValue, hti]
  · intro a h
    simp [MultivariateRing.expand] at h

end Expand

/-- When the expansion of any term in a ring over `ℚ` returns a polynomial,
the polynomial is canonical, and the term is defined at every assignment,
under every interpretation, with the value of the polynomial. -/
public theorem expand_denote {t : Term} {a : MvPoly n Fraction} (h : r.expand t = .value a)
    (I : Interp) :
    a.Canonical Rationals.model r.coefficients r.order ∧
      ∀ ρ, t.denote I ρ = some (polyValue r a ρ) :=
  expand_spec r I t a h

/-! ## Expansions that return a polynomial -/

/-- The polynomial of an expansion is canonical. -/
private theorem expand_canonical {t : Term} {a : MvPoly n Fraction} (h : r.expand t = .value a) :
    Canon r a :=
  (expand_denote r h ⟨fun _ _ => 0, fun _ _ => none, fun _ => 0⟩).1

/-- A node of a term built from numbers, powers, products, sums and variables. -/
private theorem node_cases {t x : Term} (h : NodesFrom (r.variableNames.map Term.symbol) t)
    (hx : x ∈ t.nodes) :
    (x.rank = 0 ∨ 4 ≤ x.rank ∧ x.rank ≤ 6) ∨ ∃ s ∈ r.variableNames, x = .symbol s := by
  refine (h x hx).imp_right fun ⟨y, hy, hxy⟩ => ?_
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hy
  simp only [Term.nodes, List.mem_singleton] at hxy
  exact ⟨s, hs, hxy⟩

/-- Such a term is not a constant. -/
private theorem isConstant_eq_false {t : Term}
    (h : NodesFrom (r.variableNames.map Term.symbol) t) : t.isConstant = false := by
  rcases node_cases r h (mem_nodes_self t) with hr | ⟨s, -, rfl⟩
  · cases t <;> simp_all [Term.rank, Term.isConstant]
  · rfl

/-- Such a term is a number, a variable, a power, a product or a sum. -/
private theorem shape_cases {t : Term} (h : NodesFrom (r.variableNames.map Term.symbol) t) :
    (∃ q, t = .number q) ∨ (∃ s ∈ r.variableNames, t = .symbol s) ∨ (∃ b k, t = .power b k) ∨
      (∃ c fs, t = .product c fs) ∨ ∃ c ms, t = .sum c ms := by
  rcases node_cases r h (mem_nodes_self t) with hr | h'
  · cases t <;> simp_all [Term.rank]
  · exact .inr (.inl h')

/-- The factors of a product expand into a canonical total when each factor expands. -/
private theorem expandFactors_isValue (fs : List Term)
    (hfs : ∀ f ∈ fs, ∃ g, r.expand f = .value g) :
    ∀ total, Canon r total → ∃ a, MultivariateRing.expandFactors r total fs = .value a := by
  induction fs with
  | nil => exact fun total _ => ⟨total, by simp [MultivariateRing.expandFactors]⟩
  | cons f fs ih =>
    intro total htot
    obtain ⟨g, hg⟩ := hfs f List.mem_cons_self
    obtain ⟨m, hm, hmc, -⟩ := ((ops r).2.2.2 total g htot (expand_canonical r hg)).2
    obtain ⟨a, ha⟩ := ih (fun f' hf' => hfs f' (List.mem_cons_of_mem _ hf')) m hmc
    exact ⟨a, by simp only [MultivariateRing.expandFactors, Canonical.bind_eq_bind, hg, hm,
      Canonical.bind_value, ha]⟩

/-- The monomials of a sum expand into a canonical total when each core expands. -/
private theorem expandMonomials_isValue (ms : List (ℚ × Term))
    (hms : ∀ m ∈ ms, ∃ g, r.expand m.2 = .value g) :
    ∀ total, Canon r total → ∃ a, MultivariateRing.expandMonomials r total ms = .value a := by
  induction ms with
  | nil => exact fun total _ => ⟨total, by simp [MultivariateRing.expandMonomials]⟩
  | cons m ms ih =>
    intro total htot
    obtain ⟨q, t⟩ := m
    obtain ⟨g, hg⟩ := hms (q, t) List.mem_cons_self
    obtain ⟨c, hc, hcc, -⟩ := (ops r).2.1 q
    obtain ⟨s, hs, hsc, -⟩ := ((ops r).2.2.2 g c (expand_canonical r hg) hcc).2
    obtain ⟨u, hu, huc, -⟩ := ((ops r).2.2.2 total s htot hsc).1
    obtain ⟨a, ha⟩ := ih (fun m' hm' => hms m' (List.mem_cons_of_mem _ hm')) u huc
    exact ⟨a, by simp only [MultivariateRing.expandMonomials, Canonical.bind_eq_bind, hg, hc, hs,
      hu, Canonical.bind_value, ha]⟩

/-- A term of numbers, powers, products, sums and variables, without negative powers, expands. -/
private theorem expand_ok : ∀ t : Term, NodesFrom (r.variableNames.map Term.symbol) t →
    (∀ b, b ∉ t.negBases) → ∃ a, r.expand t = .value a := by
  refine Kalyx.Proofs.Terms.term_induct (fun q => ?_) (fun c => ?_) (fun s => ?_)
    (fun hd args _ => ?_) (fun b k ih => ?_) (fun c fs ih => ?_) (fun c ms ih => ?_)
    (fun s os _ => ?_)
  all_goals intro h hn
  · obtain ⟨a, ha, -⟩ := (ops r).2.1 q
    exact ⟨a, by simp only [MultivariateRing.expand, ha]⟩
  · rcases shape_cases r h with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h
  · rcases shape_cases r h with ⟨_, h⟩ | ⟨s', hs', h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;>
      cases h
    obtain ⟨i, hi⟩ := variableIndex_isSome r hs'
    obtain ⟨a, ha, -⟩ := (ops r).1 i
    exact ⟨a, by simp only [MultivariateRing.expand, hi, ha]⟩
  · rcases shape_cases r h with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h
  · have hb : b ∈ (Term.power b k).nodes := by simp [Term.nodes, mem_nodes_self]
    obtain ⟨g, hg⟩ := ih (h.sub hb) fun x hx => hn x (by simp [Term.negBases, hx])
    have hk : ¬k < 0 := fun hk =>
      hn b (by simp [Term.negBases, hk, isConstant_eq_false r (h.sub hb)])
    obtain ⟨a, ha, -⟩ := (ops r).2.2.1 g (expand_canonical r hg) k.toNat
    exact ⟨a, by simp only [MultivariateRing.expand, Canonical.bind_eq_bind, hg,
      Canonical.bind_value, hk, ↓reduceIte, ha]⟩
  · have hfs : ∀ f ∈ fs, ∃ g, r.expand f = .value g := fun f hf =>
      ih f hf (h.sub (mem_nodes_factor hf)) fun x hx =>
        hn x (by simpa [Term.negBases] using mem_negBasesList.2 ⟨f, hf, hx⟩)
    obtain ⟨t, ht, htc, -⟩ := (ops r).2.1 c
    obtain ⟨a, ha⟩ := expandFactors_isValue r fs hfs t htc
    exact ⟨a, by simp only [MultivariateRing.expand, Canonical.bind_eq_bind, ht,
      Canonical.bind_value, ha]⟩
  · have hms : ∀ m ∈ ms, ∃ g, r.expand m.2 = .value g := fun m hm => by
      have hm2 : m.2 ∈ (Term.sum c ms).nodes := by
        simp only [Term.nodes]
        exact List.mem_cons_of_mem _ (mem_nodesPairs.2 ⟨m, hm, mem_nodes_self _⟩)
      exact ih m hm (h.sub hm2) fun x hx =>
        hn x (by simpa [Term.negBases] using mem_negBasesPairs.2 ⟨m, hm, hx⟩)
    obtain ⟨t, ht, htc, -⟩ := (ops r).2.1 c
    obtain ⟨a, ha⟩ := expandMonomials_isValue r ms hms t htc
    exact ⟨a, by simp only [MultivariateRing.expand, Canonical.bind_eq_bind, ht,
      Canonical.bind_value, ha]⟩
  · rcases shape_cases r h with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h

/-- The expansion of a term whose nodes are numbers, powers, products, sums and
the symbols of the variables of the ring, without a negative power, returns a
polynomial. -/
public theorem expand_isValue {t : Term} (h : NodesFrom (r.variableNames.map Term.symbol) t)
    (hn : ∀ b, b ∉ t.negBases) : ∃ a, r.expand t = .value a :=
  expand_ok r t h hn

/-! ## Polynomials by their values -/

/-- When the names of the variables are distinct, two canonical polynomials of
the ring with the same value at every assignment are equal. -/
public theorem eq_of_polyValue_eq (hnd : r.variableNames.Nodup) {a b : MvPoly n Fraction}
    (ha : a.Canonical Rationals.model r.coefficients r.order)
    (hb : b.Canonical Rationals.model r.coefficients r.order)
    (h : ∀ ρ, polyValue r a ρ = polyValue r b ρ) : a = b := by
  refine Canonical.eq_of_interpret_eq Rationals.model r.coefficients
    (rationalRing_exact.1.unique _) ha hb ?_
  refine MvPolynomial.map_injective (Rat.castHom ℂ) Rat.cast_injective
    (MvPolynomial.funext fun x => ?_)
  let ρ : Assignment := fun s => match r.variableIndex s with
    | some i => x i
    | none => 0
  have hx : (fun i => ρ (r.variableName i)) = x :=
    funext fun i => by simp [ρ, variableIndex_variableName r hnd i]
  have := h ρ
  rw [polyValue, polyValue, hx] at this
  simpa only [eval_map] using this

end Kalyx.Proofs.Multivariate.Expansion
