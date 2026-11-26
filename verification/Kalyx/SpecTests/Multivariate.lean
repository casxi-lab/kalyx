module

public meta import Kalyx.Spec.Multivariate.Basic
public meta import Kalyx.Spec.Multivariate.Orders
public meta import Kalyx.Spec.Multivariate.Form
public meta import Kalyx.Spec.Multivariate.Arithmetic
public meta import Kalyx.Spec.Multivariate.Terms
public meta import Kalyx.Spec.Fields.Rationals

/-!
# Replays of the vectors of the multivariate polynomials

The vectors whose answers the multivariate polynomials decide, replayed
through the specification of `Kalyx.Spec.Multivariate` with `#guard`: the
four examples of the monomial orders in the requirements of the coefficient
fields of the earlier implementation (`ex1-lex`, `ex1-grlex`, `ex1-grevlex`
and `ex7-block1`), and the rows of `vectors/cli_cases.tsv` of `mpoly` and
`poly-ring` that this specification decides.

Each ring is written out with its data: the coefficients `ℚ`, the names of
its variables and its order, as the arguments of the row name them. Reading
the arguments into a ring and a term, and the display of rings and
polynomials, belong to the command surface, which is not part of this
specification. Each input is written as an input tree `E`, unnormalized, and
`E.canonAt` builds its canonical term through the constructors of the term
core, an operator at a time, as a parse builds it, under the order
`Orders.sample` and the limit `defaultMaxExponent`; the term is then expanded
in the ring. A polynomial is compared by its terms, each exponent vector
listed in the order of the variables, with its coefficient; a term converted
back by the ring, under the same order and limit, is compared by structure
with the canonical term of the answer, built the same way; and an error is
compared by its kind.
-/

namespace Kalyx.SpecTests.Multivariate

open Kalyx.Spec.Fields (Rationals Fraction)
open Kalyx.Spec.Multivariate
open Kalyx.Spec.Terms (Term Orders mkSymbol mkSum mkSubtract mkProduct mkDivide mkNegate mkPower
  defaultMaxExponent)

/-! ## Input trees, rings and polynomials -/

/-- An input tree, as the input text writes a term: numbers, symbols, the
operators and integer powers. -/
inductive E where
  | num (q : ℚ)
  | sym (name : String)
  | add (a b : E)
  | sub (a b : E)
  | mul (a b : E)
  | div (a b : E)
  | neg (a : E)
  | pow (a : E) (k : ℤ)

meta instance (n : ℕ) : OfNat E n := ⟨.num n⟩
meta instance : Add E := ⟨.add⟩
meta instance : Sub E := ⟨.sub⟩
meta instance : Mul E := ⟨.mul⟩
meta instance : Div E := ⟨.div⟩
meta instance : Neg E := ⟨.neg⟩
meta instance : HPow E ℕ E := ⟨fun a k => .pow a k⟩
meta instance : HPow E ℤ E := ⟨fun a k => .pow a k⟩

/-- The symbol `x`. -/
meta def x : E := .sym "x"

/-- The symbol `y`. -/
meta def y : E := .sym "y"

/-- The symbol `z`. -/
meta def z : E := .sym "z"

/-- The canonical term of an input tree under `maxExponent`, built through the
constructors of the term core under the order `Orders.sample`. The first error
in the order of the input is the result. -/
meta def E.canonAt (maxExponent : ℕ) : E → Kalyx.Spec.Terms.Result Term
  | .num r => .value (.number r)
  | .sym name => mkSymbol name
  | .add a b => do mkSum Orders.sample [← a.canonAt maxExponent, ← b.canonAt maxExponent]
  | .sub a b => do
    mkSubtract Orders.sample maxExponent (← a.canonAt maxExponent) (← b.canonAt maxExponent)
  | .mul a b => do
    mkProduct Orders.sample maxExponent [← a.canonAt maxExponent, ← b.canonAt maxExponent]
  | .div a b => do
    mkDivide Orders.sample maxExponent (← a.canonAt maxExponent) (← b.canonAt maxExponent)
  | .neg a => do mkNegate Orders.sample maxExponent (← a.canonAt maxExponent)
  | .pow a k => do mkPower Orders.sample maxExponent (← a.canonAt maxExponent) k

/-- The canonical term of an input tree under the default limit, none when it
fails. -/
meta def E.term (e : E) : Option Term :=
  match e.canonAt defaultMaxExponent with
  | .value u => some u
  | _ => none

/-- The ring `ℚ[x, y]` under the order `o`. -/
meta def ring2 (o : OrderKind 2) : MultivariateRing Rationals 2 := ⟨⟨⟩, ["x", "y"], rfl, o⟩

/-- The ring `ℚ[x, y, z]` under the order `o`. -/
meta def ring3 (o : OrderKind 3) : MultivariateRing Rationals 3 := ⟨⟨⟩, ["x", "y", "z"], rfl, o⟩

/-- The polynomial of an input in the ring `r`: its canonical term expanded. -/
meta def polyOf {n : ℕ} (r : MultivariateRing Rationals n) (input : E) :
    MvResult (MvPoly n Fraction) :=
  match input.term with
  | some u => r.expand u
  | none => .fault (.term .internal)

/-- The terms of a polynomial, each exponent vector listed in the order of the
variables. -/
meta def listed {n : ℕ} (a : MvPoly n Fraction) : List (List ℕ × Fraction) :=
  a.terms.map fun t => (List.ofFn t.1, t.2)

/-- The listed terms `(e, c)` of `l`, each coefficient the reduced fraction of
`c`. -/
meta def terms (l : List (List ℕ × ℚ)) : List (List ℕ × Fraction) :=
  l.map fun (e, c) => (e, Fraction.ofRat c)

/-- The leading term of the polynomial of an input in the ring `r`, listed;
none for the zero polynomial. -/
meta def leadingOf {n : ℕ} (r : MultivariateRing Rationals n) (input : E) :
    MvResult (Option (List ℕ × Fraction)) :=
  (polyOf r input).map fun a => a.leadingTerm.map fun t => (List.ofFn t.1, t.2)

/-- The term of a polynomial converted back by the ring `r`. -/
meta def termOf {n : ℕ} (r : MultivariateRing Rationals n) (a : MvPoly n Fraction) :
    MvResult Term :=
  r.toTerm Orders.sample defaultMaxExponent a

/-- The canonical term of an answer as a result. -/
meta def answerOf (answer : E) : MvResult Term :=
  match answer.term with
  | some u => .value u
  | none => .fault (.term .internal)

/-- The result fails with `Syntax`, with any span. -/
meta def failsWithSyntax {α : Type} : MvResult α → Bool
  | .fault (.term (.syntax _)) => true
  | _ => false

/-! ## The examples of the monomial orders -/

-- ex1-lex (`Q[x,y,z]`, lex): `x^2+x*z^2+y^2*z` leads with `x^2`, the exponents (2, 0, 0) and
-- the coefficient 1
#guard leadingOf (ring3 .lex) (x ^ 2 + x * z ^ 2 + y ^ 2 * z) ==
  .value (some ([2, 0, 0], Fraction.ofRat 1))

-- ex1-grlex (`Q[x,y,z]`, grlex): the two terms of degree 3 lead, and lex takes `x*z^2`,
-- the exponents (1, 0, 2)
#guard leadingOf (ring3 .grlex) (x ^ 2 + x * z ^ 2 + y ^ 2 * z) ==
  .value (some ([1, 0, 2], Fraction.ofRat 1))

-- ex1-grevlex (`Q[x,y,z]`, grevlex): the two terms of degree 3 lead, and the smaller exponent
-- of the last variable `z` takes `y^2*z`, the exponents (0, 2, 1)
#guard leadingOf (ring3 .grevlex) (x ^ 2 + x * z ^ 2 + y ^ 2 * z) ==
  .value (some ([0, 2, 1], Fraction.ofRat 1))

-- ex7-block1 (`Q[x,y,z]`, the block order of the split 1): `x*y` and `x*z^2` tie in the first
-- block (`x`) above `y^4`, and grevlex on the second block (`y`, `z`) takes `x*z^2`
#guard leadingOf (ring3 (.block 1)) (x * y + x * z ^ 2 + y ^ 4) ==
  .value (some ([1, 0, 2], Fraction.ofRat 1))

/-! ## `vectors/cli_cases.tsv` -/

-- algebra/mpoly-expands-square (`Q[x,y]:lex`, `(x+y)^2`): the polynomial of the terms `y^2`,
-- `2*x*y` and `x^2`, the last the leading term, which converts back to the canonical term of
-- `x^2 + 2*x*y + y^2`
#guard (polyOf (ring2 .lex) ((x + y) ^ 2)).map listed ==
  .value (terms [([0, 2], 1), ([1, 1], 2), ([2, 0], 1)])
#guard (polyOf (ring2 .lex) ((x + y) ^ 2)).bind (termOf (ring2 .lex)) ==
  answerOf (x ^ 2 + 2 * x * y + y ^ 2)

-- algebra/poly-ring-rejects-repeated-variable (`x,x`, lex): `Syntax`
#guard failsWithSyntax (MultivariateRing.new (⟨⟩ : Rationals) ["x", "x"] .lex)

-- algebra/poly-ring-with-grevlex-order (`x,y`, grevlex): the ring over `Q` of the variables
-- `x, y` in this order under grevlex
#guard (MultivariateRing.new (⟨⟩ : Rationals) ["x", "y"] .grevlex).map
  (fun r => (r.variableNames, r.order)) == .value (["x", "y"], .grevlex)

end Kalyx.SpecTests.Multivariate
