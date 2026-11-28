module

public import Kalyx.Proofs.Multivariate.Expansion
public import Kalyx.Proofs.Terms.Normal
public import Kalyx.Proofs.Terms.Semantics
public import Kalyx.Proofs.Terms.Bases

/-!
# The conversion of multivariate polynomials back to terms and its meaning

An unregistered helper module of the proofs about the multivariate
polynomials; it proves no registered statement. Under a total order and a
lawful interpretation, with the rules of calls that keep every call
(`RegistryRules.empty`, which rewrite nothing, so they are closed and keep
every meaning), the constructors of the term core return canonical terms with
the meaning of their input (`canonicalFormsAreClosedAndIdempotent`,
`constructorsKeepMeanings`), and build only numbers, powers, products and sums
over the nodes of their operands, keeping, for nonnegative exponents, the bases
of negative powers of their operands and no other (`Kalyx.Proofs.Terms.Bases`). So the term of each
term `c · x^e` of a canonical polynomial, and their sum, the conversion of the
polynomial, are canonical terms whose nodes are numbers, powers, products,
sums and the symbols of the variables, without a negative power, and the
conversion has the value of the polynomial at every assignment. Its expansion
then returns a canonical polynomial with the same values
(`Kalyx.Proofs.Multivariate.Expansion.expand_denote`), which is the
polynomial itself when the names of the variables are distinct
(`Kalyx.Proofs.Multivariate.Expansion.eq_of_polyValue_eq`). When the names pass the check of the ring, each symbol
of a variable is built, and the constructors fail only with `ResourceLimit`
naming `max_exponent` (`conversionKeepsMeanings`).
-/

namespace Kalyx.Proofs.Multivariate.Conversion

open Kalyx.Spec.Fields Kalyx.Spec.Multivariate Kalyx.Statements.Multivariate MvPolynomial
open Kalyx.Spec.Terms (Term Interp Orders RegistryRules Result mkSymbol mkSum mkProduct mkPower
  zpowMeaning)
open Kalyx.Statements.Terms (NoPiecewise)
open Kalyx.Proofs.Terms (NodesFrom mem_nodes_self mem_negBasesList canonical_number)
open Kalyx.Proofs.Multivariate.Expansion

/-! ## The rules that keep every call -/

/-- The rules that keep every call rewrite nothing, so they are closed. -/
private theorem empty_closed {β : Type} [Membership Term β] (c : ℕ → Term → Prop)
    (bases : Term → β) : RegistryRules.empty.Closed c bases := by
  intro _ _ _ _ _ h
  simp [RegistryRules.empty] at h

/-- The rules that keep every call keep every image. -/
private theorem empty_keeps {V : Type} (f : Term → V) : RegistryRules.empty.Keeps f := by
  intro _ _ _ _ h
  simp [RegistryRules.empty] at h

/-- The symbol of a name, when its constructor returns it. -/
private theorem mkSymbol_value {s : String} {x : Term} (h : mkSymbol s = .value x) :
    x = .symbol s := by
  unfold mkSymbol at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact (Result.value.inj h).symm

/-- A result of the term core lifted to the polynomials is a value exactly when it is one. -/
private theorem ofResult_eq_value {α : Type} {x : Result α} {v : α} :
    MvResult.ofResult x = .value v ↔ x = .value v := by
  cases x <;> simp [MvResult.ofResult]

/-! ## Built terms -/

/-- A canonical term of numbers, powers, products, sums and variables without negative powers. -/
private def Built {n : ℕ} (r : MultivariateRing Rationals n) (o : Orders) (me : ℕ) (w : Term) :
    Prop :=
  Term.Canonical o me RegistryRules.empty w ∧ NodesFrom (r.variableNames.map Term.symbol) w ∧
    ∀ b, b ∉ w.negBases

section Constructors

variable {o : Orders} {me : ℕ} {I : Interp} {n : ℕ} (r : MultivariateRing Rationals n)

/-- Built terms hold no call of `piecewise`. -/
private theorem noPiecewise {ts : List Term} (h : ∀ t ∈ ts, Built r o me t) : NoPiecewise ts := by
  intro t ht args hc
  rcases (h t ht).2.1 _ hc with hr | ⟨s, hs, hx⟩
  · simp [Term.rank] at hr
  · obtain ⟨name, -, rfl⟩ := List.mem_map.1 hs
    simp [Term.nodes] at hx

/-- A built term is not a condition. -/
private theorem isCondition_eq_false {w : Term} (h : Built r o me w) : w.isCondition = false := by
  rcases h.2.1 w (mem_nodes_self w) with hr | ⟨s, hs, hx⟩
  · cases w <;> simp_all [Term.rank, Term.isCondition]
  · obtain ⟨name, -, rfl⟩ := List.mem_map.1 hs
    simp only [Term.nodes, List.mem_singleton] at hx
    subst hx
    rfl

/-- A number is built. -/
private theorem number_built (q : ℚ) : Built r o me (.number q) :=
  ⟨canonical_number q, .number q, by simp [Term.negBases]⟩

/-- The symbol of a variable, when its constructor returns it, is built. -/
private theorem symbol_built (ho : o.Total) (i : Fin n) {x : Term}
    (h : mkSymbol (r.variableName i) = .value x) :
    x = .symbol (r.variableName i) ∧ Built r o me x := by
  have hc := (Kalyx.Proofs.Terms.canonicalFormsAreClosedAndIdempotent o me RegistryRules.empty ho
    (empty_closed _ _)).2.2.2.2.2.2.2.1 (r.variableName i)
  rw [h] at hc
  obtain rfl := mkSymbol_value h
  refine ⟨rfl, hc, .self (List.mem_map_of_mem ?_), by simp [Term.negBases]⟩
  simp [MultivariateRing.variableName]

/-- A product of built operands is built, with the product of their values. -/
private theorem product_built (ho : o.Total) (hI : I.Lawful) {ts : List Term} {u : Term}
    (hts : ∀ t ∈ ts, Built r o me t) (h : mkProduct o me ts = .value u) :
    Built r o me u ∧ ∀ ρ, u.denote I ρ = (Term.denoteList I ρ ts).map List.prod := by
  have hc := (Kalyx.Proofs.Terms.canonicalFormsAreClosedAndIdempotent o me RegistryRules.empty ho
    (empty_closed _ _)).2.1 ts fun t ht => (hts t ht).1
  have hm := (Kalyx.Proofs.Terms.constructorsKeepMeanings o me RegistryRules.empty I ho
    (empty_closed _ _) (empty_keeps _) hI).2.1 ts u (fun t ht => (hts t ht).1) h
  obtain ⟨hN, hF⟩ := Kalyx.Proofs.Terms.Bases.mkProduct_bases h
  rw [h] at hc
  refine ⟨⟨hc, hF.trans' fun t ht => (hts t ht).2.1, fun b hb => ?_⟩, hm.1 (noPiecewise r hts)⟩
  obtain ⟨t, ht, hb⟩ := mem_negBasesList.1 ((hN b).1 hb)
  exact (hts t ht).2.2 b hb

/-- A sum of built operands is built, with the sum of their values. -/
private theorem sum_built (ho : o.Total) (hI : I.Lawful) {ts : List Term} {u : Term}
    (hts : ∀ t ∈ ts, Built r o me t) (h : mkSum o ts = .value u) :
    Built r o me u ∧ ∀ ρ, u.denote I ρ = (Term.denoteList I ρ ts).map List.sum := by
  have hc := (Kalyx.Proofs.Terms.canonicalFormsAreClosedAndIdempotent o me RegistryRules.empty ho
    (empty_closed _ _)).1 ts fun t ht => (hts t ht).1
  have hm := (Kalyx.Proofs.Terms.constructorsKeepMeanings o me RegistryRules.empty I ho
    (empty_closed _ _) (empty_keeps _) hI).1 ts u (fun t ht => (hts t ht).1) h
  obtain ⟨hN, hF⟩ := Kalyx.Proofs.Terms.Bases.mkSum_bases h
  rw [h] at hc
  refine ⟨⟨hc, hF.trans' fun t ht => (hts t ht).2.1, fun b hb => ?_⟩, hm.1 (noPiecewise r hts)⟩
  obtain ⟨t, ht, hb⟩ := mem_negBasesList.1 ((hN b).1 hb)
  exact (hts t ht).2.2 b hb

/-- A power of a built base with a nonnegative exponent is built, with the power of its value. -/
private theorem power_built (ho : o.Total) (hI : I.Lawful) {b u : Term} {k : ℤ}
    (hb : Built r o me b) (hk : 0 ≤ k) (h : mkPower o me b k = .value u) :
    Built r o me u ∧ ∀ ρ, u.denote I ρ = (b.denote I ρ).bind fun v => zpowMeaning v k := by
  have hc := (Kalyx.Proofs.Terms.canonicalFormsAreClosedAndIdempotent o me RegistryRules.empty ho
    (empty_closed _ _)).2.2.1 b k hb.1
  have hm := (Kalyx.Proofs.Terms.constructorsKeepMeanings o me RegistryRules.empty I ho
    (empty_closed _ _) (empty_keeps _) hI).2.2.1 b k u hb.1 h
  obtain ⟨hN, hF⟩ := Kalyx.Proofs.Terms.Bases.mkPower_bases hb.1 h
  rw [h] at hc
  have hbs : ∀ t ∈ [b], Built r o me t := by simpa using hb
  refine ⟨⟨hc, hF.trans' fun t ht => (hbs t ht).2.1, fun x hx => ?_⟩, hm.1 (noPiecewise r hbs)⟩
  rcases (hN x).1 hx with hx | ⟨hk', -⟩
  exacts [hb.2.2 x hx, absurd hk' (not_lt.2 hk)]

end Constructors

/-! ## The terms of the terms of a polynomial -/

section Terms

variable {o : Orders} {me : ℕ} {I : Interp} {n : ℕ} (r : MultivariateRing Rationals n)

/-- The power of a variable in a monomial is built, with the power of its value. -/
private theorem variablePower_spec (ho : o.Total) (hI : I.Lawful) (e : Exponents n) (i : Fin n)
    {w : Term} (h : r.variablePower o me e i = .value w) :
    Built r o me w ∧ ∀ ρ, w.denote I ρ = some (ρ (r.variableName i) ^ e i) := by
  unfold MultivariateRing.variablePower at h
  obtain ⟨x, hx, h⟩ := Kalyx.Proofs.Terms.bind_eq_value.1 h
  obtain ⟨rfl, hxb⟩ := symbol_built r ho i hx
  split at h
  · rename_i h1
    simp only [Kalyx.Proofs.Terms.pure_value, Result.value.injEq] at h
    subst h
    exact ⟨hxb, fun ρ => by simp [Term.denote, h1]⟩
  · obtain ⟨hwb, hwd⟩ := power_built r ho hI hxb (Int.natCast_nonneg _) h
    refine ⟨hwb, fun ρ => ?_⟩
    have hk : ¬((e i : ℤ) < 0) := by omega
    simp [hwd ρ, Term.denote, zpowMeaning, hk]

/-- The powers of the variables of a monomial are built, with their values. -/
private theorem powers_spec (ho : o.Total) (hI : I.Lawful) (e : Exponents n) :
    ∀ (l : List (Fin n)) (fs : List Term), l.mapM (r.variablePower o me e) = .value fs →
      (∀ f ∈ fs, Built r o me f) ∧
        ∀ ρ, Term.denoteList I ρ fs = some (l.map fun i => ρ (r.variableName i) ^ e i) := by
  intro l
  induction l with
  | nil =>
    intro fs h
    simp only [List.mapM_nil, Kalyx.Proofs.Terms.pure_value, Result.value.injEq] at h
    subst h
    exact ⟨by simp, fun ρ => by simp [Term.denoteList]⟩
  | cons i l ih =>
    intro fs h
    rw [List.mapM_cons] at h
    obtain ⟨w, hw, h⟩ := Kalyx.Proofs.Terms.bind_eq_value.1 h
    obtain ⟨ws, hws, h⟩ := Kalyx.Proofs.Terms.bind_eq_value.1 h
    simp only [Kalyx.Proofs.Terms.pure_value, Result.value.injEq] at h
    subst h
    obtain ⟨hwb, hwd⟩ := variablePower_spec r ho hI e i hw
    obtain ⟨hl', hld⟩ := ih ws hws
    refine ⟨fun f hf => ?_, fun ρ => by simp [Term.denoteList, hwd ρ, hld ρ]⟩
    rcases List.mem_cons.1 hf with rfl | hf
    exacts [hwb, hl' f hf]

/-- A product over a filtered list, whose other factors are one. -/
private theorem prod_filter {α M : Type} [CommMonoid M] (p : α → Bool) (f : α → M)
    (hf : ∀ a, p a = false → f a = 1) : ∀ l : List α, ((l.filter p).map f).prod = (l.map f).prod
  | [] => rfl
  | a :: l => by
    cases hpa : p a <;> simp [hpa, hf a, prod_filter p f hf l]

/-- The term of a term `c · x^e` is built and has the value `c · ρ(x)^e`. -/
private theorem monomialTerm_spec (ho : o.Total) (hI : I.Lawful) (t : Exponents n × Fraction)
    {w : Term} (h : r.monomialTerm o me t = .value w) :
    Built r o me w ∧
      ∀ ρ, w.denote I ρ = some ((t.2.interpret : ℂ) * ∏ i, ρ (r.variableName i) ^ t.1 i) := by
  unfold MultivariateRing.monomialTerm at h
  obtain ⟨fs, hfs, h⟩ := Kalyx.Proofs.Terms.bind_eq_value.1 h
  obtain ⟨hfb, hfd⟩ := powers_spec r ho hI t.1 _ fs hfs
  have hprod : ∀ ρ : Kalyx.Spec.Terms.Assignment,
      (((List.finRange n).filter fun i => t.1 i != 0).map
        fun i => ρ (r.variableName i) ^ t.1 i).prod = ∏ i, ρ (r.variableName i) ^ t.1 i := by
    intro ρ
    rw [prod_filter _ _ (fun i hi => by simp_all), Fin.prod_univ_def]
  split at h
  · simp only [Kalyx.Proofs.Terms.pure_value, Result.value.injEq] at h
    subst h
    refine ⟨number_built r _, fun ρ => ?_⟩
    have := hfd ρ
    simp only [Term.denoteList, Option.some.injEq] at this
    rw [← hprod ρ, ← this]
    simp [Term.denote]
  · have hts : ∀ f ∈ Term.number t.2.interpret :: fs, Built r o me f := by
      simpa using ⟨number_built r _, hfb⟩
    obtain ⟨hwb, hwd⟩ := product_built r ho hI hts h
    exact ⟨hwb, fun ρ => by simp [hwd ρ, Term.denoteList, Term.denote, hfd ρ, hprod ρ]⟩

/-- The terms of the terms of a list are built, with the values of the terms. -/
private theorem terms_spec (ho : o.Total) (hI : I.Lawful) :
    ∀ (l : List (Exponents n × Fraction)) (ts : List Term),
      l.mapM (r.monomialTerm o me) = .value ts → (∀ t ∈ ts, Built r o me t) ∧
        ∀ ρ, Term.denoteList I ρ ts =
          some (l.map fun t => (t.2.interpret : ℂ) * ∏ i, ρ (r.variableName i) ^ t.1 i) := by
  intro l
  induction l with
  | nil =>
    intro ts h
    simp only [List.mapM_nil, Kalyx.Proofs.Terms.pure_value, Result.value.injEq] at h
    subst h
    exact ⟨by simp, fun ρ => by simp [Term.denoteList]⟩
  | cons y l ih =>
    intro ts h
    rw [List.mapM_cons] at h
    obtain ⟨w, hw, h⟩ := Kalyx.Proofs.Terms.bind_eq_value.1 h
    obtain ⟨ws, hws, h⟩ := Kalyx.Proofs.Terms.bind_eq_value.1 h
    simp only [Kalyx.Proofs.Terms.pure_value, Result.value.injEq] at h
    subst h
    obtain ⟨hwb, hwd⟩ := monomialTerm_spec r ho hI y hw
    obtain ⟨hl', hld⟩ := ih ws hws
    refine ⟨fun f hf => ?_, fun ρ => by simp [Term.denoteList, hwd ρ, hld ρ]⟩
    rcases List.mem_cons.1 hf with rfl | hf
    exacts [hwb, hl' f hf]

/-- The value of a polynomial, term by term. -/
private theorem polyValue_eq (a : MvPoly n Fraction) (ρ : Kalyx.Spec.Terms.Assignment) :
    polyValue r a ρ =
      (a.terms.map fun t => (t.2.interpret : ℂ) * ∏ i, ρ (r.variableName i) ^ t.1 i).sum := by
  rw [polyValue, MvPoly.interpret, ← coe_eval₂Hom, map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp [eval₂_monomial, Finsupp.prod_fintype, Rationals.model]

/-- The terms of the terms of a polynomial, and their sum, when the conversion returns a term. -/
private theorem toTerm_parts {a : MvPoly n Fraction} {u : Term}
    (h : r.toTerm o me a = .value u) :
    ∃ ts, a.terms.mapM (r.monomialTerm o me) = .value ts ∧ mkSum o ts = .value u := by
  unfold MultivariateRing.toTerm at h
  rw [ofResult_eq_value] at h
  exact Kalyx.Proofs.Terms.bind_eq_value.1 h

/-- The conversion of a polynomial is built and has the value of the polynomial. -/
private theorem toTerm_spec (ho : o.Total) (hI : I.Lawful) {a : MvPoly n Fraction} {u : Term}
    (h : r.toTerm o me a = .value u) :
    Built r o me u ∧ ∀ ρ, u.denote I ρ = some (polyValue r a ρ) := by
  obtain ⟨ts, hts, hsum⟩ := toTerm_parts r h
  obtain ⟨htb, htd⟩ := terms_spec r ho hI _ ts hts
  obtain ⟨hub, hud⟩ := sum_built r ho hI htb hsum
  exact ⟨hub, fun ρ => by rw [hud ρ, htd ρ, Option.map_some, polyValue_eq]⟩

end Terms

/-! ## Failures of the conversion -/

section Failures

variable {o : Orders} {me : ℕ} {n : ℕ} (r : MultivariateRing Rationals n)

/-- A value or `ResourceLimit` naming `max_exponent`. -/
private def Ok {α : Type} (x : Result α) : Prop := x = .resourceLimit .exponent ∨ ∃ v, x = .value v

private theorem ok_bind {α β : Type} {x : Result α} {f : α → Result β} (hx : Ok x)
    (hf : ∀ v, x = .value v → Ok (f v)) : Ok (x >>= f) := by
  rcases hx with hx | ⟨v, hv⟩
  · rw [hx]
    exact .inl rfl
  · rw [hv]
    exact hf v hv

private theorem ok_mapM {α β : Type} {f : α → Result β} :
    ∀ {l : List α}, (∀ a ∈ l, Ok (f a)) → Ok (l.mapM f)
  | [], _ => .inr ⟨[], rfl⟩
  | a :: l, h => by
    rw [List.mapM_cons]
    exact ok_bind (h a List.mem_cons_self) fun v _ =>
      ok_bind (ok_mapM fun b hb => h b (List.mem_cons_of_mem _ hb)) fun vs _ => .inr ⟨v :: vs, rfl⟩

/-- A power of a symbol other than its powers 0 and 1 is a value or a limit of `max_exponent`. -/
private theorem mkPower_symbol (s : String) {k : ℤ} (h1 : k ≠ 1) (h0 : k ≠ 0) :
    Ok (mkPower o me (.symbol s) k) := by
  unfold mkPower Kalyx.Spec.Terms.checkExponent
  split
  · exact .inl rfl
  · rename_i hk
    simp [Ok, Term.isCondition, h1, h0, Kalyx.Spec.Terms.distributedPower,
      Kalyx.Spec.Terms.mergedPower, Kalyx.Spec.Terms.mergePowers, Kalyx.Spec.Terms.buildProduct,
      Kalyx.Spec.Terms.settleItems, Kalyx.Spec.Terms.mergeItems, Kalyx.Spec.Terms.sortBy,
      Kalyx.Spec.Terms.insertBy, Kalyx.Spec.Terms.mergeAdjacent, Kalyx.Spec.Terms.reduceItem,
      Kalyx.Spec.Terms.checkExponent, hk, Kalyx.Spec.Terms.Term.imaginaryUnit,
      Kalyx.Spec.Terms.rootOf, Term.depthList, Term.depth, Kalyx.Spec.Terms.ProductParts.append]

/-- The names that pass the check of a ring are built by the symbol constructor. -/
private theorem mkSymbol_of_check : ∀ (seen names : List String),
    checkVariableNames seen names = .value () → ∀ s ∈ names, mkSymbol s = .value (.symbol s)
  | _, [], _ => by simp
  | seen, name :: names, h => by
    simp only [checkVariableNames, Canonical.bind_eq_bind] at h
    obtain ⟨x, hx, h⟩ := mvBind_eq_value.1 h
    rw [ofResult_eq_value] at hx
    obtain rfl := mkSymbol_value hx
    split at h
    · cases h
    · intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      exacts [hx, mkSymbol_of_check _ names h s hs]

/-- When the symbols are built, the conversion is a term or a limit of `max_exponent`. -/
private theorem toTerm_ok (ho : o.Total) {I : Interp} (hI : I.Lawful)
    (hsym : ∀ i, mkSymbol (r.variableName i) = .value (.symbol (r.variableName i)))
    (a : MvPoly n Fraction) :
    r.toTerm o me a = .resourceLimit .exponent ∨ ∃ u, r.toTerm o me a = .value u := by
  have hsp := Kalyx.Proofs.Terms.sumsAndProductsIgnoreOrderAndGrouping o me RegistryRules.empty
    ho (empty_closed _ _)
  have hvp : ∀ e i, e i ≠ 0 → Ok (r.variablePower o me e i) := by
    intro e i hi
    unfold MultivariateRing.variablePower
    rw [hsym i, Kalyx.Proofs.Terms.bind_value]
    split
    · exact .inr ⟨_, rfl⟩
    · exact mkPower_symbol _ (by omega) (by omega)
  have hmt : ∀ t, Ok (r.monomialTerm o me t) := by
    intro t
    unfold MultivariateRing.monomialTerm
    refine ok_bind (ok_mapM fun i hi => hvp t.1 i (by simpa using (List.mem_filter.1 hi).2))
      fun fs hfs => ?_
    obtain ⟨hfb, -⟩ := powers_spec r ho hI t.1 _ fs hfs
    split
    · exact .inr ⟨_, rfl⟩
    · have hts : ∀ f ∈ Term.number t.2.interpret :: fs, Built r o me f := by
        simpa using ⟨number_built r _, hfb⟩
      rcases hsp.2.2.2.2.2.1 _ fun f hf => ⟨(hts f hf).1, isCondition_eq_false r (hts f hf)⟩ with
        ⟨u, hu⟩ | hu
      exacts [.inr ⟨u, hu⟩, .inl hu]
  have hok : Ok (do mkSum o (← a.terms.mapM (r.monomialTerm o me))) :=
    ok_bind (ok_mapM fun t _ => hmt t) fun ts hts =>
      .inr (hsp.2.2.2.2.1 ts fun t ht =>
        isCondition_eq_false r ((terms_spec r ho hI _ ts hts).1 t ht))
  unfold MultivariateRing.toTerm
  rcases hok with h | ⟨u, h⟩
  · exact .inl (by rw [h]; rfl)
  · exact .inr ⟨u, by rw [h]; rfl⟩

end Failures

/-- The conversion of a canonical polynomial of a ring over `ℚ` back to a term,
under a total order and a lawful interpretation: a term that it returns is
canonical under the rules that keep every call, has the value of the
polynomial at every assignment, and expands back into the polynomial when the
names of the variables are distinct; and when the names pass the check of the
ring, the conversion returns a term unless it fails with `ResourceLimit`
naming `max_exponent`. -/
public theorem conversionKeepsMeanings (o : Orders) (maxExponent n : ℕ)
    (r : MultivariateRing Rationals n) (I : Interp) (ho : o.Total) (hI : I.Lawful)
    (a : MvPoly n Fraction) (ha : a.Canonical Rationals.model r.coefficients r.order) :
    (∀ u, r.toTerm o maxExponent a = .value u →
      u.Canonical o maxExponent RegistryRules.empty ∧
      (∀ ρ, u.denote I ρ = some (polyValue r a ρ)) ∧
      (r.variableNames.Nodup → r.expand u = .value a)) ∧
    (checkVariableNames [] r.variableNames = .value () →
      r.toTerm o maxExponent a = .resourceLimit .exponent ∨
        ∃ u, r.toTerm o maxExponent a = .value u) := by
  refine ⟨fun u h => ?_, fun hc => toTerm_ok r ho hI (fun i => mkSymbol_of_check [] _ hc _
    (by simp [MultivariateRing.variableName])) a⟩
  obtain ⟨⟨hc, hF, hN⟩, hd⟩ := toTerm_spec r ho hI h
  refine ⟨hc, hd, fun hnd => ?_⟩
  obtain ⟨b, hb⟩ := expand_isValue r hF hN
  obtain ⟨hbc, hbd⟩ := expand_denote r hb I
  rw [hb, eq_of_polyValue_eq r hnd ha hbc fun ρ => Option.some.inj ((hd ρ).symm.trans (hbd ρ))]

end Kalyx.Proofs.Multivariate.Conversion
