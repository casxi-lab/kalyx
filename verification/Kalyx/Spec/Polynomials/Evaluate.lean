module

public import Kalyx.Spec.Polynomials.Arithmetic

/-!
# Polynomials: evaluation

Evaluation of a polynomial at an element of its coefficient ring, a shared
algorithm of the architecture ("Coefficient-field trait"; POL-R14): the sum
of the terms `c x^d` with the element in place of `x`, each power and each
product and sum formed by the operations of the coefficient ring. It is
written once, for every coefficient ring (POL-R10): it reaches the elements
only through the methods of the trait, `one`, `zero`, `multiply` and `add`,
and needs no zero test, since it builds no polynomial. The first fault or
limit of a coefficient operation ends it and is its result, passed on
unchanged; it reads no limits, and its charges are not part of this
specification. Evaluation at a polynomial, which is composition, and in
another ring through a map are not part of it.
-/

@[expose] public section

namespace Kalyx.Spec.Polynomials

open Kalyx.Spec.Fields (CoefficientRing)

variable {P E U : Type}

/-- The power `c^k` of the element `c` of the parent `p` by repeated
squaring: from one, each binary digit of `k`, from the highest, squares the
power and, for a digit 1, multiplies it by `c`. So `c^0` is one, also for
`c = 0`. -/
def elementPower (R : CoefficientRing P E U) (p : P) (c : E) (k : ℕ) : PolyResult E :=
  (binaryDigits k).foldlM (init := R.one p) fun s digit => do
    let s ← PolyResult.ofOutcome (R.multiply p s s)
    if digit then PolyResult.ofOutcome (R.multiply p s c) else pure s

/-- The value of the polynomial `a` over the parent `p` at the element `c`
(POL-R14): from zero, for each term `e x^d` in the stored order, the product
`e c^d` (`elementPower`) added to the sum. So the zero polynomial has the
value zero, and a constant term contributes its coefficient times one. -/
def Poly.eval (R : CoefficientRing P E U) (p : P) (a : Poly E) (c : E) : PolyResult E :=
  a.terms.foldlM (init := R.zero p) fun acc (d, e) => do
    let m ← PolyResult.ofOutcome (R.multiply p e (← elementPower R p c d))
    PolyResult.ofOutcome (R.add p acc m)

end Kalyx.Spec.Polynomials

end
