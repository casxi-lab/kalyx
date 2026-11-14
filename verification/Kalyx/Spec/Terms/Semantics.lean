module

public import Kalyx.Spec.Terms.Algebraic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Terms: the meaning of a term

The meaning of a term (architecture, "Meaning of a function value") is a
strict partial function from the assignments of its symbols to the complex
numbers: `Term.denote I ρ t` is `some v` where `t` is defined at `ρ` with the
value `v`, and `none` where it is undefined. A node is defined where its
children are defined and lie in the domain of its operation: a negative power
is undefined where its base is 0, and a product or a sum where any of its
parts is, the coefficient 0 of a witness included.

Numbers are their values, `π` is `Real.pi`, `i` is `Complex.I`, and symbols
take their values from the assignment. What the term core does not fix is an
interpretation, `Interp`:

* `call`, the value of a call from its head and the values of its arguments.
  The term core treats every call as a total uninterpreted atom
  (architecture, "Domains of calls"): a call is defined where its arguments
  are, and the domain of the function is carried by the condition of a
  function value, outside the term core. `derivative` and `substitute` are
  such atoms too, of the values of all their arguments, which the term core
  never rewrites. `piecewise` is the exception: its
  meaning is that of a branch where its condition is true or false, and
  undefined where its condition is undefined (architecture, "Branches").
* `cond`, the truth of a condition, true, false or undefined, from its shape
  and the meanings of its operands. Of the conditions only the truth values
  are fixed (`Interp.CondLaw`); the decision of comparisons and properties
  and the connectives are fixed with the conditions, not here.
* `algebraic`, the values of the algebraic constants.

The laws that the statements assume of an interpretation are separate
propositions: the truth values (`Interp.CondLaw`), the identities of the
function registry that the term core reads for the powers of roots
(`Interp.RootLaw`), and nonzero values of the valid constants
(`Interp.ConstantsNonzero`). Two relations of meanings name what the
statements compare: the same meaning at every assignment (`Term.SameMeaning`),
and the one direction in which a result is defined only where an input is,
with the same value there (`DefinedWithin`).

This module is not computable, and the computable modules of the
specification do not import it.
-/

@[expose] public section

namespace Kalyx.Spec.Terms

/-- An assignment of complex values to the names of symbols. -/
abbrev Assignment := String → ℂ

/-- The meaning of an operand of a condition at an assignment: a value, or
the truth of a condition; `none` where the operand is undefined. -/
inductive Meaning where
  /-- The value of an operand that is a value. -/
  | value (v : Option ℂ)
  /-- The truth of an operand that is a condition. -/
  | truth (b : Option Bool)

/-- An interpretation of what the term core does not fix: the values of calls,
the truth of conditions and the values of algebraic constants. -/
structure Interp where
  /-- The value of a call from its head and the values of its arguments. -/
  call : Head → List ℂ → ℂ
  /-- The truth of a condition from its shape and the meanings of its
  operands, `none` where it is undefined. -/
  cond : CondShape → List Meaning → Option Bool
  /-- The value of an algebraic constant, by its identity and its type; not
  read for `π` and `i`. -/
  algebraic : Constant → ℂ

/-- The value of a constant: `Complex.I` for `i`, `Real.pi` for `π`, and the
value of the interpretation for an algebraic constant. -/
noncomputable def Constant.denote (I : Interp) : Constant → ℂ
  | .named .i => Complex.I
  | .named .pi => Real.pi
  | .real id => I.algebraic (.real id)
  | .complex id => I.algebraic (.complex id)

open Classical in
/-- The integer power `x ^ k` where it is defined: undefined for a negative
power of 0, and `0 ^ 0 = 1`. -/
noncomputable def zpowMeaning (x : ℂ) (k : ℤ) : Option ℂ :=
  if x = 0 ∧ k < 0 then none else some (x ^ k)

mutual

/-- The meaning of a term at an assignment `ρ` under the interpretation `I`:
a number is its value, a constant `Constant.denote`, and a symbol its value
in `ρ`; a call `piecewise(c, a, b)` is the meaning of `a` where `c` is true,
of `b` where `c` is false, and undefined where `c` is undefined; any other
call is `I.call` of its head and the values of its arguments, where they are
all defined; a power `b ^ k` is `zpowMeaning` of the value of `b`; a product
and a sum are the product of their coefficient and their factors and the sum
of their constant and their monomials, where every part is defined; a
condition has no value. -/
noncomputable def Term.denote (I : Interp) (ρ : Assignment) : Term → Option ℂ
  | .number q => some q
  | .constant c => some (c.denote I)
  | .symbol s => some (ρ s)
  | .call h args =>
    match h, args with
    | ⟨"piecewise", .formal⟩, [c, a, b] =>
      match Term.holds I ρ c with
      | some true => Term.denote I ρ a
      | some false => Term.denote I ρ b
      | none => none
    | h, args => (Term.denoteList I ρ args).map (I.call h)
  | .power b k => (Term.denote I ρ b).bind fun x => zpowMeaning x k
  | .product c fs => (Term.denoteList I ρ fs).map fun vs => c * vs.prod
  | .sum c ms => (Term.denotePairs I ρ ms).map fun v => c + v
  | .condition .. => none
  termination_by structural t => t

/-- The truth of a condition at an assignment: `I.cond` of its shape and the
meanings of its operands. A value has no truth. -/
noncomputable def Term.holds (I : Interp) (ρ : Assignment) : Term → Option Bool
  | .condition s ops => I.cond s (Term.meanings I ρ ops)
  | _ => none
  termination_by structural t => t

/-- The values of a list of terms, where all of them are defined. -/
noncomputable def Term.denoteList (I : Interp) (ρ : Assignment) :
    List Term → Option (List ℂ)
  | [] => some []
  | t :: ts => (Term.denote I ρ t).bind fun v => (Term.denoteList I ρ ts).map (v :: ·)
  termination_by structural ts => ts

/-- The meanings of the operands of a condition, in order: the truth of each
condition and the value of each value. -/
noncomputable def Term.meanings (I : Interp) (ρ : Assignment) : List Term → List Meaning
  | [] => []
  | t :: ts =>
    (if t.isCondition then .truth (Term.holds I ρ t) else .value (Term.denote I ρ t)) ::
      Term.meanings I ρ ts
  termination_by structural ts => ts

/-- The sum of the monomials `a · t` of a list, where every core is
defined. -/
noncomputable def Term.denotePairs (I : Interp) (ρ : Assignment) : List (ℚ × Term) → Option ℂ
  | [] => some 0
  | (a, t) :: ms => (Term.denote I ρ t).bind fun v => (Term.denotePairs I ρ ms).map (a * v + ·)
  termination_by structural ms => ms

end

/-! ## Laws of an interpretation and relations of meanings -/

/-- The truth values are fixed: the condition `true` is true and `false` is
false. -/
def Interp.CondLaw (I : Interp) : Prop := ∀ b : Bool, I.cond (.truth b) [] = some b

/-- The two identities of the function registry that the term core reads for
the powers of roots, at every value `u`: `sqrt_eq_rootn`, `√u = rootn(u, 2)`;
and `root_pow`, `rootn(u, n)^k = u^⌊k/n⌋ · rootn(u, n)^(k mod n)` for a
degree `n ≥ 1` and every `k ≥ 1`. -/
def Interp.RootLaw (I : Interp) : Prop :=
  (∀ u : ℂ, I.call ⟨"sqrt", .registered⟩ [u] = I.call ⟨"rootn", .registered⟩ [u, 2]) ∧
  ∀ (u : ℂ) (n k : ℕ), 1 ≤ n → 1 ≤ k →
    I.call ⟨"rootn", .registered⟩ [u, n] ^ k =
      u ^ (k / n) * I.call ⟨"rootn", .registered⟩ [u, n] ^ (k % n)

/-- Every valid constant (`Constant.Valid`) has a value other than 0. -/
def Interp.ConstantsNonzero (I : Interp) : Prop := ∀ c : Constant, c.Valid → c.denote I ≠ 0

/-- The laws of an interpretation together. -/
def Interp.Lawful (I : Interp) : Prop := I.CondLaw ∧ I.RootLaw ∧ I.ConstantsNonzero

/-- Two terms have the same meaning: at every assignment, both are undefined,
or both are defined with the same value. This is the criterion of the rules
that the term core and the call constructor may apply (architecture, "Rules
of the call constructor"). -/
def Term.SameMeaning (I : Interp) (s t : Term) : Prop := ∀ ρ, s.denote I ρ = t.denote I ρ

/-- `g` is defined only where `f` is, with the same value there: wherever `g`
is `some v`, `f` is `some v`. Of the meaning `g` of the result of a
construction and the strict meaning `f` of its input, it says that the result
gives no value where the input is undefined and no other value where it is
defined, while it may be undefined where the input is defined. -/
def DefinedWithin (g f : Assignment → Option ℂ) : Prop :=
  ∀ ρ v, g ρ = some v → f ρ = some v

end Kalyx.Spec.Terms

end
