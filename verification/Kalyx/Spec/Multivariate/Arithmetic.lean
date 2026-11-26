module

public import Kalyx.Spec.Multivariate.Form

/-!
# Multivariate polynomials: the ring operations

The operations of a ring of multivariate polynomials (MVP-R05, FLD-R03): one,
the variable at a position, constants, negation, sums and differences,
products and powers by repeated squaring; the zero polynomial is
`MvPoly.zero`. Each is written once, for every coefficient ring whose zero
test always decides (MVP-R04): it reaches the coefficients only through the
methods of the trait (`CoefficientRing`), its element operations and its zero
test, takes the parent of the coefficient ring and the monomial order from
the ring `r` that it is given, obtains no element of the coefficient ring
from an integer but its one, and divides no coefficient, so it holds in
every characteristic.

The coefficient operations of an operation run in a fixed order, which
decides its first fault, and no term whose coefficient the zero test finds
zero is kept:

* a sum or a difference merges the terms of its operands in increasing
  monomials under the order of the ring; the coefficients of a monomial that
  both operands have are added or subtracted, and their result is tested for
  zero;
* a product multiplies every term of its left operand by every term of its
  right one, then gathers the products into the polynomial of their terms by
  `MvPoly.normalize`, which adds the coefficients of each monomial and drops
  the terms whose coefficient is zero;
* a power squares and multiplies by the binary digits of its exponent.

The first fault or limit of a coefficient operation ends the operation and
is its result, passed on unchanged. On canonical operands, over a coefficient
ring with the ring laws, every result is canonical and denotes the result of
the same operation of Mathlib on the polynomials that the operands denote;
these are statements about the definitions. The operations read no limits:
the checks of the limits and the storage cost of a result, and the work that
each step charges, are not part of this specification.
-/

@[expose] public section

namespace Kalyx.Spec.Multivariate

open Kalyx.Spec.Fields (CoefficientRing Outcome)

variable {P E : Type} {n : ℕ}

/-! ## Loops over terms

The loops over the terms of the operands over the parent `p` of the
coefficient ring, each a list of terms in the stored order. -/

/-- The terms of a list in their order, each with the coefficient `f c` and
without a zero test: the negation of each coefficient, which is not zero when
the coefficient is not, in every ring; or the terms of a merge that only the
right operand has. -/
def MvPoly.mapCoefficients (f : E → Outcome E) :
    List (Exponents n × E) → MvResult (List (Exponents n × E))
  | [] => .value []
  | (e, c) :: ts => do
    let c ← MvResult.ofOutcome (f c)
    pure ((e, c) :: (← MvPoly.mapCoefficients f ts))
  termination_by structural ts => ts

/-- One step of a merge under the order `o`: the term `t` of the left
operand, whose later terms the merge `rest` takes, with the terms of the
right operand. The term of the lower monomial comes first: `t` alone is
written as it is, before the merge of the rest; a term `c' · x^e` of the
right operand alone is written with the coefficient `alone c'`, before the
step goes on; and two terms of the same monomial give the coefficient
`combine c c'`, which is tested for zero and written only when it is not
zero. -/
def MvPoly.mergeStep (R : CoefficientRing P E Empty) (p : P) (o : OrderKind n)
    (combine : E → E → Outcome E) (alone : E → Outcome E) (t : Exponents n × E)
    (rest : List (Exponents n × E) → MvResult (List (Exponents n × E))) :
    List (Exponents n × E) → MvResult (List (Exponents n × E))
  | [] => do pure (t :: (← rest []))
  | u :: us =>
    match o.compare t.1 u.1 with
    | .lt => do pure (t :: (← rest (u :: us)))
    | .gt => do
      let c ← MvResult.ofOutcome (alone u.2)
      pure ((u.1, c) :: (← MvPoly.mergeStep R p o combine alone t rest us))
    | .eq => do
      let c ← MvResult.ofOutcome (combine t.2 u.2)
      let vanishes ← testZero R p c
      let tail ← rest us
      pure (if vanishes then tail else (t.1, c) :: tail)
  termination_by structural us => us

/-- The merge of the terms `as` of the left operand with the terms `bs` of
the right one under the order `o`, both strictly increasing under it: each
step takes the term of the lower monomial, or the two terms of the same
monomial, as `MvPoly.mergeStep` states, so the result is strictly increasing
as well. The terms of the right operand after the last term of the left one
take the coefficient `alone c'`. -/
def MvPoly.merge (R : CoefficientRing P E Empty) (p : P) (o : OrderKind n)
    (combine : E → E → Outcome E) (alone : E → Outcome E) :
    List (Exponents n × E) → List (Exponents n × E) → MvResult (List (Exponents n × E))
  | [], bs => MvPoly.mapCoefficients alone bs
  | t :: as, bs => MvPoly.mergeStep R p o combine alone t (MvPoly.merge R p o combine alone as) bs
  termination_by structural as _ => as

/-- The products of the term `t` with the terms of a list, in their order:
for each term `c' · x^e`, the monomial `x^d · x^e`, the sum of the exponent
vectors, with the coefficient `c · c'` of the coefficient ring, where `t` is
`c · x^d`. No coefficient is tested here. -/
def MvPoly.scaledTerms (R : CoefficientRing P E Empty) (p : P) (t : Exponents n × E) :
    List (Exponents n × E) → MvResult (List (Exponents n × E))
  | [] => .value []
  | u :: us => do
    let c ← MvResult.ofOutcome (R.multiply p t.2 u.2)
    pure ((Exponents.product t.1 u.1, c) :: (← MvPoly.scaledTerms R p t us))
  termination_by structural us => us

/-- The products of each term of a list, in their order, with the terms `bs`
of the other operand, in their order (`MvPoly.scaledTerms`): the terms of a
product before they are gathered. -/
def MvPoly.termProducts (R : CoefficientRing P E Empty) (p : P) (bs : List (Exponents n × E)) :
    List (Exponents n × E) → MvResult (List (Exponents n × E))
  | [] => .value []
  | t :: ts => do
    let row ← MvPoly.scaledTerms R p t bs
    pure (row ++ (← MvPoly.termProducts R p bs ts))
  termination_by structural ts => ts

/-- The binary digits of `k`, the highest first, after the digits `acc`; `k`
is the part whose digits remain, and `fuel`, at least the number of those
digits, bounds the recursion. -/
def binaryDigitsFrom : ℕ → ℕ → List Bool → List Bool
  | 0, _, acc => acc
  | fuel + 1, k, acc =>
    if k = 0 then acc else binaryDigitsFrom fuel (k / 2) ((k % 2 == 1) :: acc)
  termination_by structural fuel _ _ => fuel

/-- The binary digits of `k`, the highest first; none for `0`. -/
def binaryDigits (k : ℕ) : List Bool := binaryDigitsFrom k k []

/-! ## The operations

Each operation of the ring `r`, with `R` the methods of its coefficient
ring. The operations take polynomials of `r`, built by its operations or by
an equal ring, and never compare rings. -/

namespace MultivariateRing

/-- `one`: the one of the coefficient ring at the constant monomial, the zero
polynomial when the zero test finds it zero, as in a ring where `1 = 0`. -/
def one (R : CoefficientRing P E Empty) (r : MultivariateRing P n) : MvResult (MvPoly n E) :=
  MvPoly.monomial R r.coefficients Exponents.constant (R.one r.coefficients)

/-- `generator`, the variable at the position `i`, which is below the number
of variables by its type: the one of the coefficient ring at the monomial of
that variable, the zero polynomial when the zero test finds it zero. -/
def generator (R : CoefficientRing P E Empty) (r : MultivariateRing P n) (i : Fin n) :
    MvResult (MvPoly n E) :=
  MvPoly.monomial R r.coefficients (Exponents.generator i) (R.one r.coefficients)

/-- `constant`: the element `c` of the coefficient ring at the constant
monomial, the zero polynomial when the zero test finds it zero. -/
def constant (R : CoefficientRing P E Empty) (r : MultivariateRing P n) (c : E) :
    MvResult (MvPoly n E) :=
  MvPoly.monomial R r.coefficients Exponents.constant c

/-- `negate`: each coefficient negated, without a zero test, the monomials
kept. -/
def negate (R : CoefficientRing P E Empty) (r : MultivariateRing P n) (a : MvPoly n E) :
    MvResult (MvPoly n E) :=
  (MvPoly.mapCoefficients (R.negate r.coefficients) a.terms).map MvPoly.mk

/-- `add`: the merge of the terms of `a` and `b` under the order of the ring,
whose coefficients of one monomial are added, a term of either operand alone
kept as it is. -/
def add (R : CoefficientRing P E Empty) (r : MultivariateRing P n) (a b : MvPoly n E) :
    MvResult (MvPoly n E) :=
  (MvPoly.merge R r.coefficients r.order (R.add r.coefficients) .value a.terms b.terms).map
    MvPoly.mk

/-- `subtract`: the merge of the terms of `a` and `b` under the order of the
ring, whose coefficients of one monomial are subtracted, a term of the
subtrahend alone negated. -/
def subtract (R : CoefficientRing P E Empty) (r : MultivariateRing P n) (a b : MvPoly n E) :
    MvResult (MvPoly n E) :=
  (MvPoly.merge R r.coefficients r.order (R.subtract r.coefficients) (R.negate r.coefficients)
    a.terms b.terms).map MvPoly.mk

/-- `multiply`: the product of each term of `a`, in their order, with each
term of `b`, in their order (`MvPoly.termProducts`), then the polynomial of
these products in the ring (`MultivariateRing.normalize`), which sorts them by
the order of the ring, adds the coefficients of each monomial and drops the
terms whose coefficient the zero test finds zero, such as a product of two
zero divisors. So a product with the zero polynomial is the zero
polynomial. -/
def multiply (R : CoefficientRing P E Empty) (r : MultivariateRing P n) (a b : MvPoly n E) :
    MvResult (MvPoly n E) := do
  r.normalize R (← MvPoly.termProducts R r.coefficients b.terms a.terms)

/-- `power` with the exponent `k` (FLD-R03): for `k = 0` the polynomial one
(`MultivariateRing.one`), also for `a = 0`; for `k ≥ 1` the power starts
from `a`, and each binary digit of `k` below the highest, from the top,
squares it and, when the digit is 1, multiplies it by `a`, each a product of
the ring. So `0ᵏ = 0` for `k ≥ 1`. -/
def power (R : CoefficientRing P E Empty) (r : MultivariateRing P n) (a : MvPoly n E) (k : ℕ) :
    MvResult (MvPoly n E) :=
  if k = 0 then r.one R
  else (binaryDigits k).tail.foldlM (init := a) fun s digit => do
    let s ← r.multiply R s s
    if digit then r.multiply R s a else pure s

end MultivariateRing

end Kalyx.Spec.Multivariate

end
