module

public import Kalyx.Spec.Polynomials.Storage

/-!
# Polynomials: the ring operations and the derivative

The operations of a polynomial ring (polynomials contract, "Operations"):
zero, one, the variable `x` and constants, negation, sums and differences,
products, powers by repeated squaring and the derivative by the variable.
Each is written once, for every coefficient ring whose zero test always
decides (FLD-R04, POL-R10): it reaches the coefficients only through the
methods of the trait (`CoefficientRing`), its element operations, its zero
test and, for the checks, its `measure`; it obtains integers only as
`fromInteger n`, the element `n · 1`, and divides no coefficient, so it holds
in every characteristic.

Each operation has two layers. The operations without the checks, over the
parent `p` of the coefficient ring (`Poly.negate`, `Poly.sum`,
`Poly.difference`, `Poly.product`, `Poly.derivative`), compute the terms of
the result in increasing degree by the coefficient operations in the order of
kalyx, each computed coefficient tested for zero and written only when it is
not zero (`Poly.appendNonzero`); the first fault or limit of a coefficient
operation ends the operation and is its result, passed on unchanged
(FLD-R12). The operations of the ring `r` under the limits `L`
(`PolynomialRing.add` and the others) then check the result
(`PolynomialRing.check`): its degree against `max_exponent`, then its
storage cost against `max_nodes` and `max_storage_bytes`. A product checks
every partial sum of its rows as well, and a product, a power and the
variable check a degree before they compute anything (FLD-R03). The shared
algorithms take the arithmetic without the checks, so it too exists once.
The work that each step charges is not part of this specification.
-/

@[expose] public section

namespace Kalyx.Spec.Polynomials

open Kalyx.Spec.Fields (CoefficientRing Outcome)

variable {P E : Type}

/-! ## Loops over terms -/

/-- The terms `(d, c)` of a list written above `acc` in order, each with the
coefficient `f c` and without a zero test: the negation of each coefficient,
which is not zero when the coefficient is not, in every ring; or the terms of
a merge that only one operand has. -/
def Poly.appendEach (f : E → Outcome E) : Poly E → List (ℕ × E) → PolyResult (Poly E)
  | acc, [] => .value acc
  | acc, (d, c) :: rest => do
    let c ← PolyResult.ofOutcome (f c)
    Poly.appendEach f (← acc.append d c) rest
termination_by structural _ l => l

/-- One step of a merge of the term `c x^d` of the left operand, whose other
terms `rest` merges, with the terms of the right operand, written above
`acc`. The term of lower degree comes first: a term of the left operand alone
is written as it is, and a term `c' x^e` of the right operand alone with the
coefficient `alone c'`; two terms of the same degree give the coefficient
`combine c c'`, which is tested for zero. -/
def Poly.mergeStep (R : CoefficientRing P E Empty) (p : P) (combine : E → E → Outcome E)
    (alone : E → Outcome E) (d : ℕ) (c : E)
    (rest : Poly E → List (ℕ × E) → PolyResult (Poly E)) :
    Poly E → List (ℕ × E) → PolyResult (Poly E)
  | acc, [] => do rest (← acc.append d c) []
  | acc, (e, c') :: bs =>
    if d < e then do rest (← acc.append d c) ((e, c') :: bs)
    else if e < d then do
      let c' ← PolyResult.ofOutcome (alone c')
      Poly.mergeStep R p combine alone d c rest (← acc.append e c') bs
    else do
      let s ← PolyResult.ofOutcome (combine c c')
      rest (← acc.appendNonzero R p d s) bs
termination_by structural _ l => l

/-- The merge of the terms `as` of the left operand with the terms `bs` of the
right one, written above `acc`, in increasing degree (polynomials contract,
"Sums and differences"): each step takes the term of lower degree, or the two
terms of the same degree, as `Poly.mergeStep` states. -/
def Poly.merge (R : CoefficientRing P E Empty) (p : P) (combine : E → E → Outcome E)
    (alone : E → Outcome E) :
    List (ℕ × E) → Poly E → List (ℕ × E) → PolyResult (Poly E)
  | [], acc, bs => acc.appendEach alone bs
  | (d, c) :: as, acc, bs =>
    Poly.mergeStep R p combine alone d c (Poly.merge R p combine alone as) acc bs
termination_by structural l _ _ => l

/-- The row `c x^d · q` of a product over the parent `p`, written above `acc`:
for each term `c' x^e` of `q` in order, the coefficient `c · c'`, tested for
zero, since it can be zero in a ring with zero divisors, at the degree
`d + e`. -/
def Poly.row (R : CoefficientRing P E Empty) (p : P) (d : ℕ) (c : E) :
    Poly E → List (ℕ × E) → PolyResult (Poly E)
  | acc, [] => .value acc
  | acc, (e, c') :: q => do
    let m ← PolyResult.ofOutcome (R.multiply p c c')
    Poly.row R p d c (← acc.appendNonzero R p (d + e) m) q
termination_by structural _ l => l

/-- The terms of the derivative over the parent `p` of the terms of a list,
written above `acc`: each term `c x^d` with `d ≥ 1` gives the coefficient
`(d · 1) c`, the product of `fromInteger d` and `c` in the coefficient ring,
tested for zero, at the degree `d - 1`; a constant term vanishes. -/
def Poly.derivativeTerms (R : CoefficientRing P E Empty) (p : P) :
    Poly E → List (ℕ × E) → PolyResult (Poly E)
  | acc, [] => .value acc
  | acc, (0, _) :: rest => Poly.derivativeTerms R p acc rest
  | acc, (d + 1, c) :: rest => do
    let m ← PolyResult.ofOutcome (R.multiply p (R.fromInteger p (d + 1 : ℕ)) c)
    Poly.derivativeTerms R p (← acc.appendNonzero R p d m) rest
termination_by structural _ l => l

/-- The binary digits of `k`, the highest first, after the digits `acc`; `n`
is the part of `k` whose digits remain, and `fuel`, at least the number of
those digits, bounds the recursion. -/
def binaryDigitsFrom : ℕ → ℕ → List Bool → List Bool
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    if n = 0 then acc else binaryDigitsFrom fuel (n / 2) ((n % 2 == 1) :: acc)
termination_by structural fuel _ _ => fuel

/-- The binary digits of `k`, the highest first; none for `0`. -/
def binaryDigits (k : ℕ) : List Bool := binaryDigitsFrom k k []

/-! ## The operations without the checks

The operations over the parent `p` of the coefficient ring, without the
checks of their results: the arithmetic that the checked operations below
add the checks to, and that the shared algorithms use. -/

/-- The negation of `a`: each coefficient negated, without a zero test. -/
def Poly.negate (R : CoefficientRing P E Empty) (p : P) (a : Poly E) : PolyResult (Poly E) :=
  Poly.zero.appendEach (R.negate p) a.terms

/-- The sum of `a` and `b`: the merge whose coefficients of one degree are
added, a term of either operand alone kept as it is. -/
def Poly.sum (R : CoefficientRing P E Empty) (p : P) (a b : Poly E) : PolyResult (Poly E) :=
  Poly.merge R p (R.add p) .value a.terms Poly.zero b.terms

/-- The difference of `a` and `b`: the merge whose coefficients of one degree
are subtracted, a term of the subtrahend alone negated. -/
def Poly.difference (R : CoefficientRing P E Empty) (p : P) (a b : Poly E) :
    PolyResult (Poly E) :=
  Poly.merge R p (R.subtract p) (R.negate p) a.terms Poly.zero b.terms

/-- The rows of a product, each term `c x^d` of a list giving the row
`c x^d · q` of the other operand, whose terms are `q`, merged into the total
as a sum is, after which `check` takes the total. kalyx appends a row whose
degrees all lie above the degree of the total instead of merging it; the
merge gives the same terms, without a coefficient operation. -/
def Poly.rows (R : CoefficientRing P E Empty) (p : P) (check : Poly E → PolyResult (Poly E))
    (q : List (ℕ × E)) : Poly E → List (ℕ × E) → PolyResult (Poly E)
  | total, [] => .value total
  | total, (d, c) :: rest => do
    let w ← Poly.zero.row R p d c q
    let total ← check (← Poly.sum R p total w)
    Poly.rows R p check q total rest
termination_by structural _ l => l

/-- The product of `a` and `b`, with `check` taking every partial sum: the
rows of the operand with fewer terms, the left one when both have as many,
over the other, from the zero polynomial. The product is the last total, and
the zero polynomial when there is no row. Without the checks, `check` is
`.value`. -/
def Poly.product (R : CoefficientRing P E Empty) (p : P) (check : Poly E → PolyResult (Poly E))
    (a b : Poly E) : PolyResult (Poly E) :=
  if b.terms.length < a.terms.length then Poly.rows R p check a.terms Poly.zero b.terms
  else Poly.rows R p check b.terms Poly.zero a.terms

/-- The derivative of `a` by the variable: the terms of
`Poly.derivativeTerms`. -/
def Poly.derivative (R : CoefficientRing P E Empty) (p : P) (a : Poly E) : PolyResult (Poly E) :=
  Poly.zero.derivativeTerms R p a.terms

/-! ## The operations

Each operation of the ring `r` under the limits `L`, with `R` the methods of
its coefficient ring. -/

namespace PolynomialRing

/-- `zero`: the zero polynomial, checked as every result. -/
def zero (R : CoefficientRing P E Empty) (L : Limits) (r : PolynomialRing P) :
    PolyResult (Poly E) :=
  r.check R L Poly.zero

/-- `one`: the one of the coefficient ring at the degree 0, the zero
polynomial when the zero test finds it zero, as in a ring where `1 = 0`. -/
def one (R : CoefficientRing P E Empty) (L : Limits) (r : PolynomialRing P) :
    PolyResult (Poly E) := do
  r.check R L (← Poly.monomial R r.coefficients 0 (R.one r.coefficients))

/-- `generator`, the polynomial `x`: the check of its degree 1, then the one of
the coefficient ring at the degree 1, the zero polynomial when the zero test
finds it zero. -/
def generator (R : CoefficientRing P E Empty) (L : Limits) (r : PolynomialRing P) :
    PolyResult (Poly E) :=
  checkDegree L 1 fun _ => do
    r.check R L (← Poly.monomial R r.coefficients 1 (R.one r.coefficients))

/-- `constant`: the element `c` at the degree 0, the zero polynomial when the
zero test finds it zero. -/
def constant (R : CoefficientRing P E Empty) (L : Limits) (r : PolynomialRing P) (c : E) :
    PolyResult (Poly E) := do
  r.check R L (← Poly.monomial R r.coefficients 0 c)

/-- `negate`: the negation (`Poly.negate`), checked. -/
def negate (R : CoefficientRing P E Empty) (L : Limits) (r : PolynomialRing P) (a : Poly E) :
    PolyResult (Poly E) := do
  r.check R L (← Poly.negate R r.coefficients a)

/-- `add`: the sum (`Poly.sum`), checked. -/
def add (R : CoefficientRing P E Empty) (L : Limits) (r : PolynomialRing P) (a b : Poly E) :
    PolyResult (Poly E) := do
  r.check R L (← Poly.sum R r.coefficients a b)

/-- `subtract`: the difference (`Poly.difference`), checked. -/
def subtract (R : CoefficientRing P E Empty) (L : Limits) (r : PolynomialRing P)
    (a b : Poly E) : PolyResult (Poly E) := do
  r.check R L (← Poly.difference R r.coefficients a b)

/-- `multiply`: when neither operand is zero, the check of the degree
`deg a + deg b` first; then the product (`Poly.product`), every total checked
as a result is; then the check of the product, which repeats the check of the
last total, or checks the zero polynomial when there is no row. -/
def multiply (R : CoefficientRing P E Empty) (L : Limits) (r : PolynomialRing P)
    (a b : Poly E) : PolyResult (Poly E) :=
  let compute : Unit → PolyResult (Poly E) := fun _ => do
    r.check R L (← Poly.product R r.coefficients (r.check R L) a b)
  match a.degree, b.degree with
  | some m, some n => checkDegree L (m + n) compute
  | _, _ => compute ()

/-- `power` with the exponent `k` (FLD-R03): the check of `k`, then of the
degree `k · deg a`; then for `k = 0` the polynomial one (`PolynomialRing.one`),
also for `a = 0`; for `k ≥ 1` the power starts from `a`, and each binary
digit of `k` below the highest, from the top, squares it and, when the digit
is 1, multiplies it by `a`, each as a product with its checks; the result is
checked. So `0ᵏ = 0` for `k ≥ 1`. -/
def power (R : CoefficientRing P E Empty) (L : Limits) (r : PolynomialRing P) (a : Poly E)
    (k : ℕ) : PolyResult (Poly E) :=
  checkDegree L k fun _ => checkDegree L (k * a.degree.getD 0) fun _ =>
    if k = 0 then r.one R L
    else do
      let s ← (binaryDigits k).tail.foldlM (init := a) fun s digit => do
        let s ← r.multiply R L s s
        if digit then r.multiply R L s a else pure s
      r.check R L s

/-- `derivative` by the variable (POL-R07): the derivative
(`Poly.derivative`), checked. -/
def derivative (R : CoefficientRing P E Empty) (L : Limits) (r : PolynomialRing P)
    (a : Poly E) : PolyResult (Poly E) := do
  r.check R L (← Poly.derivative R r.coefficients a)

end PolynomialRing

end Kalyx.Spec.Polynomials

end
