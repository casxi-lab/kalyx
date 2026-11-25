module

public import Kalyx.Spec.Polynomials.Arithmetic
public import Kalyx.Spec.Terms.Call

/-!
# Polynomials: the ring of a variable, expansion and conversion back to terms

The polynomials meet the terms of the term core (`Kalyx.Spec.Terms`) here
(polynomials contract, "Expansion", "Conversion back to terms",
"Differentiation" and "Expansion and differentiation of a request"):

* `PolynomialRing.new`, the ring of a coefficient ring and a variable, whose
  name follows the rule of symbol names of the term core (POL-R01);
* `PolynomialRing.expand`, the polynomial of a canonical term in `ℚ[x]`
  (POL-R04), with the depth of the term checked at the entry (POL-R09) and the
  failures in the order of the walk (POL-R05);
* `PolynomialRing.toTerm`, the canonical term of a polynomial of `ℚ[x]`, built
  through the constructors of the term core (POL-R06);
* `PolynomialRing.differentiate`, the derivative of a term by the variable
  (POL-R07);
* `expandOperation` and `diffOperation`, the operations `expand` and `diff` of
  a request, which check the variable before they read the input (POL-R02).

Every polynomial is built by the operations of the ring of
`Kalyx.Spec.Polynomials.Arithmetic` under the limits `L`, so each is checked
as a result is (POL-R03). The constructors of the term core read the order of
terms `o` and `L.maxExponent`; a polynomial term holds no condition and no
algebraic constant, so its canonical term does not depend on the order. The
charges and the stack of the walk are not part of this specification.
-/

@[expose] public section

namespace Kalyx.Spec.Polynomials

open Kalyx.Spec.Fields (CoefficientRing Rationals Fraction)
open Kalyx.Spec.Terms (Term Orders mkSymbol mkSum mkProduct mkPower)

/-! ## The ring of a variable -/

/-- `PolynomialRing::new`: the ring over the parent `coefficients` with the
variable `name` (POL-R01), when `name` is a symbol name: a name of the wrong
form fails with `Syntax` and the span of its first character that the form
does not allow, the empty span at 0 for the empty name, and a reserved name,
`pi`, `i` or `undefined`, with `Unsupported` and the span of the whole name,
as the symbol constructor `mkSymbol` fails. -/
def PolynomialRing.new {P : Type} (coefficients : P) (name : String) :
    PolyResult (PolynomialRing P) :=
  (PolyResult.ofResult (mkSymbol name)).map fun _ => ⟨coefficients, name⟩

/-- The rationals as the coefficient ring of the polynomials of terms. -/
def rationalRing : CoefficientRing Rationals Fraction Empty := Rationals.field.toCoefficientRing

/-! ## Expansion -/

mutual

/-- The polynomial of a node of a term in the ring `r` over `ℚ` under the
limits `L`, in the order of the walk (POL-R04, POL-R05): a number is the
constant of its value; a symbol is the variable `x` when its name is the name
of the variable, and otherwise fails with `UnknownSymbol`; a power `b ^ k`
expands its base first, then fails with `NotPolynomial` for `k < 0` and is
otherwise the power of the polynomial of its base; a product starts from the
constant of its coefficient and multiplies it by the polynomial of each
factor in turn (`PolynomialRing.expandFactors`); a sum starts from the
constant of its constant and adds each monomial in turn
(`PolynomialRing.expandMonomials`). A call fails with `NotPolynomial` before
its arguments, and so do a constant, which is not a rational number, and a
condition, which is not a value. -/
def PolynomialRing.expandNode (L : Limits) (r : PolynomialRing Rationals) :
    Term → PolyResult (Poly Fraction)
  | .number q => r.constant rationalRing L (Fraction.ofRat q)
  | .constant _ => .fault .notPolynomial
  | .symbol s =>
    if s = r.variableName then r.generator rationalRing L else .fault (.term .unknownSymbol)
  | .call .. => .fault .notPolynomial
  | .power b k => do
    let base ← PolynomialRing.expandNode L r b
    if k < 0 then .fault .notPolynomial else r.power rationalRing L base k.toNat
  | .product c fs => do
    PolynomialRing.expandFactors L r (← r.constant rationalRing L (Fraction.ofRat c)) fs
  | .sum c ms => do
    PolynomialRing.expandMonomials L r (← r.constant rationalRing L (Fraction.ofRat c)) ms
  | .condition .. => .fault .notPolynomial
  termination_by structural t => t

/-- The factors of a product in their stored order, each expanded and then
multiplied into the total, the total the left operand. -/
def PolynomialRing.expandFactors (L : Limits) (r : PolynomialRing Rationals)
    (total : Poly Fraction) : List Term → PolyResult (Poly Fraction)
  | [] => .value total
  | f :: fs => do
    let factor ← PolynomialRing.expandNode L r f
    PolynomialRing.expandFactors L r (← r.multiply rationalRing L total factor) fs
  termination_by structural fs => fs

/-- The monomials `a · t` of a sum in their stored order: after the core `t`
is expanded, the constant of the coefficient `a` is built, the polynomial of
the core is multiplied by it, and the product is added to the total. The
witness monomial, whose coefficient is 0, holds a negative power and fails at
its core. -/
def PolynomialRing.expandMonomials (L : Limits) (r : PolynomialRing Rationals)
    (total : Poly Fraction) : List (ℚ × Term) → PolyResult (Poly Fraction)
  | [] => .value total
  | (a, t) :: ms => do
    let core ← PolynomialRing.expandNode L r t
    let scaled ← r.multiply rationalRing L core (← r.constant rationalRing L (Fraction.ofRat a))
    PolynomialRing.expandMonomials L r (← r.add rationalRing L total scaled) ms
  termination_by structural ms => ms

end

/-- `expand`: the polynomial of the canonical term `t` in the ring `r` over
`ℚ` under the limits `L` (POL-R04). The depth of `t` is checked first, before
anything else, and a term deeper than `maxDepth` fails with `ResourceLimit`
naming `max_depth` (POL-R09); then the nodes are walked from the root, each
node before its children and the children in their stored order
(`PolynomialRing.expandNode`), and the first failure is the result (POL-R05).
Coefficients that cancel leave no term. -/
def PolynomialRing.expand (L : Limits) (r : PolynomialRing Rationals) (t : Term) :
    PolyResult (Poly Fraction) :=
  if L.maxDepth < t.depth then .resourceLimit .depth else r.expandNode L t

/-! ## Conversion back to terms -/

/-- The term of the term `c x^k` of a polynomial over `ℚ`, with `x` the term
of the variable: the number `c` for `k = 0`, the product of `c` and `x` for
`k = 1`, and the product of `c` and the power `x^k` for `k ≥ 2`, each built
by the constructors of the term core under the order `o` and
`maxExponent`. -/
def monomialTerm (o : Orders) (maxExponent : ℕ) (x : Term) :
    ℕ × Fraction → Terms.Result Term
  | (0, c) => .value (.number c.interpret)
  | (1, c) => mkProduct o maxExponent [.number c.interpret, x]
  | (k, c) => do mkProduct o maxExponent [.number c.interpret, ← mkPower o maxExponent x k]

/-- `to_term`: the canonical term of the polynomial `a` of the ring `r` over
`ℚ` (POL-R06), built only through the constructors of the term core under the
order `o` and `L.maxExponent`: the symbol of the variable, built once by
`mkSymbol` when a term has a positive degree and otherwise not built, then
the term of each term in increasing degree (`monomialTerm`), and their sum
(`mkSum`). So the zero polynomial is the number 0 and a polynomial of one
term is the term of that term. -/
def PolynomialRing.toTerm (o : Orders) (L : Limits) (r : PolynomialRing Rationals)
    (a : Poly Fraction) : PolyResult Term :=
  PolyResult.ofResult do
    let x ← if a.terms.any (·.1 != 0) then mkSymbol r.variableName
      else .value (.symbol r.variableName)
    mkSum o (← a.terms.mapM (monomialTerm o L.maxExponent x))

/-- `differentiate`: the derivative of the term `t` by the variable of the
ring `r` over `ℚ`, as a term (POL-R07): the expansion of `t`, the derivative
of its polynomial and the conversion of the derivative back to a term, in
this order, each with its checks and failures. -/
def PolynomialRing.differentiate (o : Orders) (L : Limits) (r : PolynomialRing Rationals)
    (t : Term) : PolyResult Term := do
  r.toTerm o L (← r.derivative rationalRing L (← r.expand L t))

/-! ## The operations of a request -/

/-- A fault of a name without its span: the faults of the variable of a
request carry none. -/
def PolyFault.withoutSpan : PolyFault → PolyFault
  | .term (.syntax _) => .term (.syntax none)
  | .term (.unsupported _) => .term (.unsupported none)
  | k => k

/-- The ring `ℚ[x]` of the variable `name` of a request (POL-R02): the ring of
`PolynomialRing.new`, whose faults of the name lose their spans. Names are
compared byte by byte, so they are case-sensitive. -/
def requestRing (name : String) : PolyResult (PolynomialRing Rationals) :=
  match PolynomialRing.new (⟨⟩ : Rationals) name with
  | .fault k => .fault k.withoutSpan
  | result => result

/-- The operation `expand` of a request with the variable `name` and the input
term `input` under the order `o` and the limits `L` (POL-R02): the variable
is checked first, before the input is read; then the canonical term of the
polynomial of the input, its expansion converted back to a term with the
same ring. -/
def expandOperation (o : Orders) (L : Limits) (name : String) (input : Term) :
    PolyResult Term := do
  let r ← requestRing name
  r.toTerm o L (← r.expand L input)

/-- The operation `diff` of a request with the variable `name` and the input
term `input` under the order `o` and the limits `L` (POL-R02): the variable
is checked first, before the input is read; then the derivative of the input
by the variable (`PolynomialRing.differentiate`). -/
def diffOperation (o : Orders) (L : Limits) (name : String) (input : Term) :
    PolyResult Term := do
  (← requestRing name).differentiate o L input

end Kalyx.Spec.Polynomials

end
