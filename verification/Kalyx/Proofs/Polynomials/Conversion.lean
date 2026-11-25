module

public import Kalyx.Proofs.Polynomials.Expansion
public import Kalyx.Proofs.Terms.Semantics
public import Kalyx.Proofs.Terms.Normal

/-!
# The conversion of polynomials back to terms and its meaning

An unregistered helper module of the proofs about the univariate polynomials;
it proves no registered statement. Under a total order and a lawful
interpretation, with the rules of calls that keep every call
(`RegistryRules.empty`, which rewrite nothing, so they are closed and keep
every meaning), the constructors of the term core return canonical terms
without calls on canonical operands without calls, with the meaning of their
input (`Kalyx.Proofs.Terms`). So the term of each term `c xᵈ` of a canonical
polynomial is canonical, holds no call and has the value `c ρ(x)ᵈ`, and the
sum of these terms, the conversion of the polynomial, has the value of the
polynomial at every assignment (`toTerm_denote`).
-/

namespace Kalyx.Proofs.Polynomials.Conversion

open Kalyx.Spec.Fields Kalyx.Spec.Polynomials Kalyx.Statements.Polynomials Polynomial
open Kalyx.Spec.Terms (Term Interp Orders RegistryRules mkSymbol mkSum mkProduct mkPower
  zpowMeaning)
open Kalyx.Statements.Terms (NoPiecewise CallsWithin)
open Kalyx.Proofs.Polynomials.Expansion

/-! ## The rules that keep every call -/

/-- The rules that keep every call rewrite nothing, so they are closed. -/
public theorem empty_closed {β : Type} [Membership Term β] (c : ℕ → Term → Prop)
    (bases : Term → β) : RegistryRules.empty.Closed c bases := by
  intro _ _ _ _ _ h
  simp [RegistryRules.empty] at h

/-- The rules that keep every call keep every image. -/
public theorem empty_keeps {V : Type} (f : Term → V) : RegistryRules.empty.Keeps f := by
  intro _ _ _ _ h
  simp [RegistryRules.empty] at h

/-! ## Constructors on operands without calls -/

/-- No node of the term is a call. -/
private abbrev NoCalls (t : Term) : Prop := ∀ h args, Term.call h args ∉ t.nodes

/-- The canonical form under the rules that keep every call. -/
private abbrev Canon (o : Orders) (me : ℕ) (t : Term) : Prop :=
  Term.Canonical o me RegistryRules.empty t

section Constructors

variable {o : Orders} {me : ℕ} {I : Interp}

private theorem noCalls_of_within {u : Term} {ts : List Term} (h : CallsWithin u ts)
    (hts : ∀ t ∈ ts, NoCalls t) : NoCalls u := by
  intro hd args hu
  obtain ⟨t, ht, hmem⟩ := h hd args hu
  exact hts t ht hd args hmem

private theorem noCalls_number (q : ℚ) : NoCalls (.number q) := by
  intro _ _ hm
  simp [Term.nodes] at hm

private theorem noCalls_symbol (s : String) : NoCalls (.symbol s) := by
  intro _ _ hm
  simp [Term.nodes] at hm

/-- A product of canonical operands without calls. -/
private theorem product_meaning (ho : o.Total) (hI : I.Lawful) {ts : List Term} {u : Term}
    (hts : ∀ t ∈ ts, Canon o me t ∧ NoCalls t) (h : mkProduct o me ts = .value u) :
    Canon o me u ∧ NoCalls u ∧ ∀ ρ, u.denote I ρ = (Term.denoteList I ρ ts).map List.prod := by
  have hc := (Kalyx.Proofs.Terms.canonicalFormsAreClosedAndIdempotent o me RegistryRules.empty ho
    (empty_closed _ _)).2.1 ts fun t ht => (hts t ht).1
  have hm := (Kalyx.Proofs.Terms.constructorsKeepMeanings o me RegistryRules.empty I ho
    (empty_closed _ _) (empty_keeps _) hI).2.1 ts u (fun t ht => (hts t ht).1) h
  have ha := (Kalyx.Proofs.Terms.callsAreAtoms o me RegistryRules.empty ho
    (empty_closed _ _)).2.1 ts u (fun t ht => (hts t ht).1) h
  rw [h] at hc
  exact ⟨hc, noCalls_of_within ha fun t ht => (hts t ht).2,
    hm.1 fun t ht args => (hts t ht).2 _ args⟩

/-- A power of a canonical base without calls. -/
private theorem power_meaning (ho : o.Total) (hI : I.Lawful) {b u : Term} {k : ℤ}
    (hb : Canon o me b ∧ NoCalls b) (h : mkPower o me b k = .value u) :
    Canon o me u ∧ NoCalls u ∧ ∀ ρ, u.denote I ρ = (b.denote I ρ).bind fun v => zpowMeaning v k := by
  have hc := (Kalyx.Proofs.Terms.canonicalFormsAreClosedAndIdempotent o me RegistryRules.empty ho
    (empty_closed _ _)).2.2.1 b k hb.1
  have hm := (Kalyx.Proofs.Terms.constructorsKeepMeanings o me RegistryRules.empty I ho
    (empty_closed _ _) (empty_keeps _) hI).2.2.1 b k u hb.1 h
  have ha := (Kalyx.Proofs.Terms.callsAreAtoms o me RegistryRules.empty ho
    (empty_closed _ _)).2.2.1 b k u hb.1 h
  rw [h] at hc
  refine ⟨hc, noCalls_of_within ha fun t ht => ?_, hm.1 fun t ht args => ?_⟩
  · rw [List.mem_singleton] at ht
    exact ht ▸ hb.2
  · rw [List.mem_singleton] at ht
    exact ht ▸ hb.2 _ args

/-- A sum of canonical operands without calls. -/
private theorem sum_meaning (ho : o.Total) (hI : I.Lawful) {ts : List Term} {u : Term}
    (hts : ∀ t ∈ ts, Canon o me t ∧ NoCalls t) (h : mkSum o ts = .value u) :
    ∀ ρ, u.denote I ρ = (Term.denoteList I ρ ts).map List.sum :=
  ((Kalyx.Proofs.Terms.constructorsKeepMeanings o me RegistryRules.empty I ho
    (empty_closed _ _) (empty_keeps _) hI).1 ts u (fun t ht => (hts t ht).1) h).1
    fun t ht args => (hts t ht).2 _ args

end Constructors

/-! ## The meaning of the conversion -/

section ToTerm

variable {o : Orders} {I : Interp}

/-- The term of a term `c xᵈ` with the canonical symbol `x` of the name `s`
is canonical, holds no call and has the value `c ρ(s)ᵈ`. -/
private theorem monomialTerm_spec (ho : o.Total) (hI : I.Lawful) (me : ℕ) (s : String)
    (d : ℕ) (f : Fraction) {t : Term} (hx : d ≠ 0 → Canon o me (.symbol s))
    (h : monomialTerm o me (.symbol s) (d, f) = .value t) :
    Canon o me t ∧ NoCalls t ∧ ∀ ρ, t.denote I ρ = some ((f.interpret : ℂ) * ρ s ^ d) := by
  rcases d with _ | _ | d
  · simp only [monomialTerm, Kalyx.Spec.Terms.Result.value.injEq] at h
    subst h
    exact ⟨Kalyx.Proofs.Terms.canonical_number _, noCalls_number _, fun ρ => by simp [Term.denote]⟩
  · simp only [monomialTerm] at h
    have hts : ∀ t ∈ [Term.number f.interpret, .symbol s], Canon o me t ∧ NoCalls t := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨⟨Kalyx.Proofs.Terms.canonical_number _, noCalls_number _⟩,
        ⟨hx one_ne_zero, noCalls_symbol _⟩⟩
    obtain ⟨htc, htn, htd⟩ := product_meaning ho hI hts h
    exact ⟨htc, htn, fun ρ => by simp [htd, Term.denoteList, Term.denote]⟩
  · simp only [monomialTerm] at h
    obtain ⟨w, hw, h⟩ := Kalyx.Proofs.Terms.bind_eq_value.1 h
    obtain ⟨hwc, hwn, hwd⟩ := power_meaning ho hI ⟨hx (by omega), noCalls_symbol s⟩ hw
    have hts : ∀ t ∈ [Term.number f.interpret, w], Canon o me t ∧ NoCalls t := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨⟨Kalyx.Proofs.Terms.canonical_number _, noCalls_number _⟩, ⟨hwc, hwn⟩⟩
    obtain ⟨htc, htn, htd⟩ := product_meaning ho hI hts h
    refine ⟨htc, htn, fun ρ => ?_⟩
    have hwv : w.denote I ρ = some (ρ s ^ (d + 2)) := by
      rw [hwd ρ]
      simp only [Term.denote, Option.bind_some, zpowMeaning]
      split
      · rename_i hc
        exact absurd hc.2 (by omega)
      · rw [zpow_natCast]
    simp [htd, Term.denoteList, Term.denote, hwv]

/-- The terms of the terms of a list with canonical coefficients. -/
private theorem mapM_spec (ho : o.Total) (hI : I.Lawful) (me : ℕ) (s : String) :
    ∀ (l : List (ℕ × Fraction)) (ts : List Term), (∀ y ∈ l, y.1 ≠ 0 → Canon o me (.symbol s)) →
      l.mapM (monomialTerm o me (.symbol s)) = .value ts →
      (∀ t ∈ ts, Canon o me t ∧ NoCalls t) ∧
        ∀ ρ, Term.denoteList I ρ ts = some (l.map fun y => (y.2.interpret : ℂ) * ρ s ^ y.1) := by
  intro l
  induction l with
  | nil =>
    intro ts _ h
    simp only [List.mapM_nil, Kalyx.Proofs.Terms.pure_value,
      Kalyx.Spec.Terms.Result.value.injEq] at h
    subst h
    exact ⟨by simp, fun ρ => by simp [Term.denoteList]⟩
  | cons y l ih =>
    intro ts hx h
    obtain ⟨d, f⟩ := y
    rw [List.mapM_cons] at h
    obtain ⟨t, ht, h⟩ := Kalyx.Proofs.Terms.bind_eq_value.1 h
    obtain ⟨ts', hts', h⟩ := Kalyx.Proofs.Terms.bind_eq_value.1 h
    simp only [Kalyx.Proofs.Terms.pure_value, Kalyx.Spec.Terms.Result.value.injEq] at h
    subst h
    obtain ⟨htc, htn, htd⟩ := monomialTerm_spec (I := I) ho hI me s d f
      (hx (d, f) List.mem_cons_self) ht
    obtain ⟨hl, hld⟩ := ih ts' (fun y hy => hx y (List.mem_cons_of_mem _ hy)) hts'
    refine ⟨fun t' ht' => ?_, fun ρ => ?_⟩
    · rcases List.mem_cons.1 ht' with rfl | ht'
      · exact ⟨htc, htn⟩
      · exact hl t' ht'
    · simp [Term.denoteList, htd ρ, hld ρ]

/-- A result of the term core lifted to the polynomials is a value exactly when
it is one. -/
public theorem ofResult_eq_value {α : Type} {x : Kalyx.Spec.Terms.Result α} {v : α} :
    PolyResult.ofResult x = .value v ↔ x = .value v := by
  cases x <;> simp [PolyResult.ofResult]

/-- The symbol of a name, when its constructor returns it. -/
public theorem mkSymbol_value {s : String} {x : Term} (h : mkSymbol s = .value x) :
    x = .symbol s := by
  unfold mkSymbol at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact (Kalyx.Spec.Terms.Result.value.inj h).symm

/-- The conversion of a polynomial whose result is a value: the symbol of the
variable, and the terms of the terms whose sum is the result. -/
public theorem toTerm_parts {L : Limits} {r : PolynomialRing Rationals} {a : Poly Fraction}
    {u : Term} (h : r.toTerm o L a = .value u) :
    (a.terms.any (·.1 != 0) = true → ∃ x, mkSymbol r.variableName = .value x) ∧
    ∃ ts, a.terms.mapM (monomialTerm o L.maxExponent (.symbol r.variableName)) = .value ts ∧
      mkSum o ts = .value u := by
  unfold PolynomialRing.toTerm at h
  rw [ofResult_eq_value] at h
  by_cases hany : (a.terms.any fun y => y.1 != 0) = true
  · simp only [hany, ↓reduceIte] at h
    obtain ⟨x, hx, h⟩ := Kalyx.Proofs.Terms.bind_eq_value.1 h
    have hxs := mkSymbol_value hx
    subst hxs
    obtain ⟨ts, hts, h⟩ := Kalyx.Proofs.Terms.bind_eq_value.1 h
    exact ⟨fun _ => ⟨_, hx⟩, ts, hts, h⟩
  · simp only [hany, Bool.false_eq_true, ↓reduceIte, Kalyx.Proofs.Terms.bind_value] at h
    obtain ⟨ts, hts, h⟩ := Kalyx.Proofs.Terms.bind_eq_value.1 h
    exact ⟨fun h' => absurd h' hany, ts, hts, h⟩

/-- Under a total order and a lawful interpretation, the conversion of a
polynomial back to a term has the value of the polynomial at every
assignment. -/
public theorem toTerm_denote (ho : o.Total) (hI : I.Lawful) {L : Limits}
    {r : PolynomialRing Rationals} {a : Poly Fraction} {u : Term} (h : r.toTerm o L a = .value u)
    (ρ : Kalyx.Spec.Terms.Assignment) : u.denote I ρ = some (polyValue r a ρ) := by
  obtain ⟨hsym, ts, hts, hsum⟩ := toTerm_parts h
  have hx : ∀ y ∈ a.terms, y.1 ≠ 0 → Canon o L.maxExponent (.symbol r.variableName) := by
    intro y hy hy0
    obtain ⟨x, hx⟩ := hsym (List.any_eq_true.2 ⟨y, hy, by simpa using hy0⟩)
    have hc := (Kalyx.Proofs.Terms.canonicalFormsAreClosedAndIdempotent o L.maxExponent
      RegistryRules.empty ho (empty_closed _ _)).2.2.2.2.2.2.2.1 r.variableName
    rw [hx] at hc
    exact mkSymbol_value hx ▸ hc
  obtain ⟨htc, htd⟩ := mapM_spec (I := I) ho hI L.maxExponent r.variableName a.terms ts hx hts
  rw [sum_meaning ho hI htc hsum ρ, htd ρ, Option.map_some]
  congr 1
  rw [polyValue, Poly.interpret, eval₂_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun y _ => ?_
  simp [eval₂_monomial, Rationals.model]

end ToTerm

end Kalyx.Proofs.Polynomials.Conversion
