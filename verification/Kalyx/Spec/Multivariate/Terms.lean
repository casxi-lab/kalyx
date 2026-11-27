module

public import Kalyx.Spec.Multivariate.Arithmetic
public import Kalyx.Spec.Fields.Rationals
public import Kalyx.Spec.Terms.Call

/-!
# Multivariate polynomials: expansion and conversion back to terms

The multivariate polynomials over `ℚ` meet the terms of the term core
(`Kalyx.Spec.Terms`) here:

* `MultivariateRing.variableName` and `MultivariateRing.variableIndex`, the
  name of the variable at a position and the position of a name;
* `MultivariateRing.expand`, the polynomial of a canonical term in a ring
  over `ℚ` (MVP-R06), with the failures in the order of the walk;
* `MultivariateRing.toTerm`, the canonical term of a polynomial of a ring
  over `ℚ` (MVP-R07), built only through the constructors of the term core.

Every polynomial of an expansion is built by the operations of the ring of
`Kalyx.Spec.Multivariate.Arithmetic`, so it is canonical whenever they are.
The constructors of the term core read the order of terms `o` and the bound
`maxExponent`, which the conversion back to terms takes as parameters, and
their faults and limits are passed on; a polynomial term holds no condition
and no algebraic constant, so its canonical term does not depend on the
order. The checks of the limits, the depth of a term at the entry and the
charges of the walk are not part of this specification.
-/

@[expose] public section

namespace Kalyx.Spec.Multivariate

open Kalyx.Spec.Fields (CoefficientRing Rationals Fraction)
open Kalyx.Spec.Terms (Term Orders mkSymbol mkSum mkProduct mkPower)

variable {n : ℕ}

/-! ## Variables by name -/

/-- The name of the variable at the position `i` of the ring `r`, which is
below the number of variables by its type. -/
def MultivariateRing.variableName {P : Type} (r : MultivariateRing P n) (i : Fin n) : String :=
  r.variableNames.get (Fin.cast r.length_variableNames.symm i)

/-- The position of the variable named `s` in the ring `r`, the first of
that name; none when no variable has it. Names are compared byte by byte, so
they are case-sensitive. -/
def MultivariateRing.variableIndex {P : Type} (r : MultivariateRing P n) (s : String) :
    Option (Fin n) :=
  (r.variableNames.finIdxOf? s).map (Fin.cast r.length_variableNames)

/-- The rationals as the coefficient ring of the polynomials of terms. -/
def rationalRing : CoefficientRing Rationals Fraction Empty := Rationals.field.toCoefficientRing

/-! ## Expansion -/

mutual

/-- `expand`: the polynomial of the canonical term `t` in the ring `r` over
`ℚ` (MVP-R06). The nodes are walked from the root, each node before its
children and the children in their stored order, and the first failure is
the result: a number is the constant of its value; a symbol is the variable
of `r` of its name (`MultivariateRing.variableIndex`), and otherwise fails
with `UnknownSymbol`; a power `b ^ k` expands its base first, then fails
with `NotPolynomial` for `k < 0` and is otherwise the power of the
polynomial of its base; a product starts from the constant of its
coefficient and multiplies it by the polynomial of each factor in turn
(`MultivariateRing.expandFactors`); a sum starts from the constant of its
constant and adds each monomial in turn
(`MultivariateRing.expandMonomials`). A call fails with `NotPolynomial`
before its arguments, and so do a constant, which is not a rational number,
and a condition, which is not a value. Coefficients that cancel leave no
term. -/
def MultivariateRing.expand (r : MultivariateRing Rationals n) :
    Term → MvResult (MvPoly n Fraction)
  | .number q => r.constant rationalRing (Fraction.ofRat q)
  | .constant _ => .fault .notPolynomial
  | .symbol s =>
    match r.variableIndex s with
    | some i => r.generator rationalRing i
    | none => .fault (.term .unknownSymbol)
  | .call .. => .fault .notPolynomial
  | .power b k => do
    let base ← MultivariateRing.expand r b
    if k < 0 then .fault .notPolynomial else r.power rationalRing base k.toNat
  | .product c fs => do
    MultivariateRing.expandFactors r (← r.constant rationalRing (Fraction.ofRat c)) fs
  | .sum c ms => do
    MultivariateRing.expandMonomials r (← r.constant rationalRing (Fraction.ofRat c)) ms
  | .condition .. => .fault .notPolynomial
  termination_by structural t => t

/-- The factors of a product in their stored order, each expanded and then
multiplied into the total, the total the left operand. -/
def MultivariateRing.expandFactors (r : MultivariateRing Rationals n)
    (total : MvPoly n Fraction) : List Term → MvResult (MvPoly n Fraction)
  | [] => .value total
  | f :: fs => do
    let factor ← MultivariateRing.expand r f
    MultivariateRing.expandFactors r (← r.multiply rationalRing total factor) fs
  termination_by structural fs => fs

/-- The monomials `a · t` of a sum in their stored order: after the core `t`
is expanded, the constant of the coefficient `a` is built, the polynomial of
the core is multiplied by it, and the product is added to the total. The
witness monomial, whose coefficient is 0, holds a negative power and fails at
its core. -/
def MultivariateRing.expandMonomials (r : MultivariateRing Rationals n)
    (total : MvPoly n Fraction) : List (ℚ × Term) → MvResult (MvPoly n Fraction)
  | [] => .value total
  | (a, t) :: ms => do
    let core ← MultivariateRing.expand r t
    let scaled ← r.multiply rationalRing core (← r.constant rationalRing (Fraction.ofRat a))
    MultivariateRing.expandMonomials r (← r.add rationalRing total scaled) ms
  termination_by structural ms => ms

end

/-! ## Conversion back to terms -/

/-- The power of the variable at the position `i` of the ring `r` in the
monomial `e`, for a positive exponent `e i`: the symbol of its name, built
by `mkSymbol`, for the exponent 1, and otherwise its power, built by
`mkPower` under the order `o` and `maxExponent`. -/
def MultivariateRing.variablePower {P : Type} (o : Orders) (maxExponent : ℕ)
    (r : MultivariateRing P n) (e : Exponents n) (i : Fin n) : Terms.Result Term := do
  let x ← mkSymbol (r.variableName i)
  if e i = 1 then pure x else mkPower o maxExponent x (e i : ℤ)

/-- The term of the term `c · x^e` of a polynomial of the ring `r` over `ℚ`:
the powers of the variables whose exponent in `e` is positive, in the order
of the variables (`MultivariateRing.variablePower`); then the number `c` when
there is none, which is the constant monomial, and otherwise the product of
the number `c` and these powers, built by `mkProduct` under the order `o` and
`maxExponent`. -/
def MultivariateRing.monomialTerm (o : Orders) (maxExponent : ℕ)
    (r : MultivariateRing Rationals n) (t : Exponents n × Fraction) : Terms.Result Term := do
  let powers ← ((List.finRange n).filter fun i => t.1 i != 0).mapM
    (r.variablePower o maxExponent t.1)
  match powers with
  | [] => pure (.number t.2.interpret)
  | fs => mkProduct o maxExponent (.number t.2.interpret :: fs)

/-- `to_term`: the canonical term of the polynomial `a` of the ring `r` over
`ℚ` (MVP-R07), built only through the constructors of the term core under
the order `o` and `maxExponent`: the term of each term in the stored order
(`MultivariateRing.monomialTerm`), and their sum (`mkSum`). So the zero
polynomial is the number 0 and a polynomial of one term is the term of that
term. The first fault or limit of a constructor is the result. -/
def MultivariateRing.toTerm (o : Orders) (maxExponent : ℕ) (r : MultivariateRing Rationals n)
    (a : MvPoly n Fraction) : MvResult Term :=
  MvResult.ofResult do mkSum o (← a.terms.mapM (r.monomialTerm o maxExponent))

end Kalyx.Spec.Multivariate

end
