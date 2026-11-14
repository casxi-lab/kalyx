module

public import Kalyx.Spec.Terms.Product

/-!
# Terms: powers, negation, differences and quotients

The canonical integer power `b ^ k` (terms contract, "Powers" and "Strict
numeric evaluation"; architecture, "Constants"; TRM-R05 to TRM-R07,
TRM-R13, TRM-R14), under an explicit `maxExponent`:

1. The exponent `k` is checked against `maxExponent` before anything else
   (`checkExponent`). A condition as the base then fails with `Syntax`.
2. A numeric base is evaluated strictly, by the integer power of the
   rationals (`ratPowOp`): `0⁰ = 1`, and a negative power of 0 fails with
   `DivisionByZero`. The bound on the bits of the result belongs to the
   rationals, and is not part of this specification.
3. The exponent 1 gives the base.
4. The exponent 0 gives `powerZero`: 1, or the ones of the maximal elements
   of `N` of the base.
5. A power distributes over a product, `(c ∏ f)ᵏ = cᵏ ∏ fᵏ`: `cᵏ` is
   computed strictly, so a product with the coefficient 0 raised to a
   negative power fails with `DivisionByZero`; each `fᵏ` follows rule 7, and
   the canonical product of the results is built.
6. A sum `s = c · p` gives `cᵏ pᵏ`, with `cᵏ` computed strictly and the
   product assembled as for products, which is `pᵏ` alone for `cᵏ = 1`.
7. For any other base, while the base is a power `cʲ` for which the merge
   condition holds, `j k < 0`, or `j, k ≥ 0`, or `j = 0`, the power
   `(cʲ)ᵏ` becomes `c^(j k)`, and `j k` is checked (`mergePowers`). Then the
   exponent 1 gives the base, the exponent 0 `powerZero`, and any other
   exponent the item `(b, k)` assembled as a product, where the powers of
   `i` and of roots reduce (`buildProduct`); for any other base this is the
   power node `b ^ k`.
8. A power of a sum is not expanded.

So `(x⁻¹)² = x⁻²` and `(x²)³ = x⁶`, while `(x⁻¹)⁻¹` stays; every power of a
one `(b⁻¹)⁰` is the one itself; `i⁻³ = i`; and for a root `s = ³√x`,
`s⁶ = x²` while `s²` and `s⁻²` stay.

`mkNegate` multiplies by `-1`; `mkSubtract` adds the negation of its second
operand; `mkDivide` multiplies by the power `-1` of the divisor, which it
builds first, so that `1/0` fails with `DivisionByZero` when it is built.
-/

@[expose] public section

namespace Kalyx.Spec.Terms

open Kalyx.Spec.Fields (ratPowOp)

/-- Whether a power `(cʲ)ᵏ` merges into `c^(j k)`: when `j k < 0`, when
`j, k ≥ 0`, or when `j = 0`; then no base that occurs with a negative
exponent is lost. -/
def mergeCondition (j k : ℤ) : Bool :=
  decide (j * k < 0) || (decide (0 ≤ j) && decide (0 ≤ k)) || j == 0

/-- The base and the exponent of `b ^ k` after the merges of rule 7: while
the base is a power `cʲ` for which the merge condition holds, `(cʲ)ᵏ`
becomes `c^(j k)`, with `j k` checked against `maxExponent`. -/
def mergePowers (maxExponent : ℕ) : Term → ℤ → Result (Term × ℤ)
  | .power c j, k =>
    if mergeCondition j k then
      checkExponent maxExponent (j * k) fun _ => mergePowers maxExponent c (j * k)
    else .value (.power c j, k)
  | b, k => .value (b, k)
  termination_by structural b _ => b

/-- Rule 7: the power `b ^ k` of a base `b` other than a number or a
product, with `k` already checked and other than 0 and 1, where a sum is a
primitive factor of a product: after the merges, the base for the exponent
1, `powerZero` for 0, and otherwise the item assembled as a product. -/
def mergedPower (o : Orders) (maxExponent : ℕ) (b : Term) (k : ℤ) : Result Term := do
  let (c, j) ← mergePowers maxExponent b k
  if j = 1 then pure c
  else if j = 0 then pure (powerZero o c)
  else buildProduct o maxExponent ⟨1, [(c, j)], []⟩

/-- Rules 5 to 7: the power `b ^ k` of a base that is not a number, with `k`
already checked and other than 0 and 1. -/
def distributedPower (o : Orders) (maxExponent : ℕ) : Term → ℤ → Result Term
  | .product c fs, k => do
    let ck ← Result.ofOutcome (ratPowOp c k)
    let rs ← fs.mapM fun f => mergedPower o maxExponent f k
    mkProduct o maxExponent (.number ck :: rs)
  | .sum c ms, k => do
    let ck ← Result.ofOutcome (ratPowOp (sumContent c ms) k)
    buildProduct o maxExponent ⟨ck, [(primitivePart c ms, k)], []⟩
  | b, k => mergedPower o maxExponent b k

/-- The canonical power `b ^ k` (`Term::power`), whose order is `o`, under
`maxExponent`: the exponent checked first, a condition rejected, then rules
2 to 7. -/
def mkPower (o : Orders) (maxExponent : ℕ) (b : Term) (k : ℤ) : Result Term :=
  checkExponent maxExponent k fun _ =>
    if b.isCondition then .fault (.syntax none)
    else match b with
      | .number r => (Result.ofOutcome (ratPowOp r k)).map .number
      | b =>
        if k = 1 then .value b
        else if k = 0 then .value (powerZero o b)
        else distributedPower o maxExponent b k

/-- The bases that a negative power of a factor `b` holds in `N`: none for
a number, a constant, a one or a condition; for a power `cʲ`, the power
itself when `j < 0`, and `c` when `j > 0` unless `c` is a constant; for a
sum, its primitive part; and for any other term, a symbol or a call, the
term itself. -/
def Term.introducedBase : Term → List Term
  | .number _ | .constant _ | .condition .. => []
  | .power c j => if j < 0 then [.power c j] else if j = 0 ∨ c.isConstant then [] else [c]
  | .sum c ms => [primitivePart c ms]
  | t => [t]

/-- The bases that the negative power of `b` that `mkPower` and `mkDivide`
introduce holds in `N` (terms contract, "Introduced negative powers"): those
of each factor of a product, and otherwise those of `b` as a factor. -/
def Term.introducedBases : Term → List Term
  | .product _ fs => fs.flatMap Term.introducedBase
  | b => b.introducedBase

/-- The negation of `t` (`negate`): the product of `-1` and `t`. -/
def mkNegate (o : Orders) (maxExponent : ℕ) (t : Term) : Result Term :=
  mkProduct o maxExponent [.number (-1), t]

/-- The difference `a - b` (`subtract`): the sum of `a` and the negation of
`b`. -/
def mkSubtract (o : Orders) (maxExponent : ℕ) (a b : Term) : Result Term := do
  let nb ← mkNegate o maxExponent b
  mkSum o [a, nb]

/-- The quotient `a / b` (`divide`): the power `-1` of `b`, built first,
and then the product of `a` and that power. -/
def mkDivide (o : Orders) (maxExponent : ℕ) (a b : Term) : Result Term := do
  let r ← mkPower o maxExponent b (-1)
  mkProduct o maxExponent [a, r]

end Kalyx.Spec.Terms

end
