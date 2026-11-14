module

public import Kalyx.Spec.Terms.Witness

/-!
# Terms: sums

The canonical sum of a list of terms (terms contract, "Sums" and "Scaling
and primitive parts of sums"; TRM-R01, TRM-R04, TRM-R05), and the scaling,
the content and the primitive part of a sum, which products and powers use
as well:

1. **Flattening** (`sumParts`): a number adds into the constant; a sum adds
   its constant and gives its monomials, its witness monomial included; a
   product `c · F` gives the monomial of `c` and the core `F` without its
   coefficient (`productCore`); any other term `t` gives the monomial
   `1 · t`. Constants and coefficients are added exactly.
2. **Merging** (`mergeMonomials`): the monomials are sorted by core in the
   order of terms, and monomials of one core add their coefficients.
3. **Cancellation** (`cancelMonomials`): the monomials whose coefficient is
   0 are removed, and the bases that they hold with a negative exponent and
   that no remaining core holds with one are kept by a single witness
   monomial with the coefficient 0 over their maximal elements, at its place
   among the cores.
4. **Assembly** (`assembleSum`): no monomial gives the constant; the
   constant 0 and one monomial give that monomial, its core for the
   coefficient 1 and otherwise the product of the coefficient and the
   factors of the core, which is the zero witness for the witness monomial;
   anything else is a sum node.

A sum takes values only: a condition among its operands fails with `Syntax`
(TRM-R15). A sum never fails otherwise, and reads no limit.
-/

@[expose] public section

namespace Kalyx.Spec.Terms

/-! ## Scaling, content and primitive part -/

/-- The sum of the constant `c` and the monomials `ms` scaled by a number
`a`: the constant and every coefficient multiplied by `a`, over the same
cores in the same order. For `a` other than 0 and 1 this is the product of
`a` and the sum; the witness monomial keeps its coefficient 0. -/
def scaleSum (a c : ℚ) (ms : List (ℚ × Term)) : Term :=
  .sum (a * c) (ms.map fun m => (a * m.1, m.2))

/-- The content of the sum of the constant `c` and the monomials `ms`: the
coefficient of its first monomial, in the order of the cores, whose
coefficient is not 0, or its constant when there is none, as when its only
monomial is the witness monomial. The content of a canonical sum is never
0. -/
def sumContent (c : ℚ) : List (ℚ × Term) → ℚ
  | [] => c
  | (a, _) :: ms => if a = 0 then sumContent c ms else a
  termination_by structural ms => ms

/-- The primitive part of the sum of `c` and `ms`: the sum scaled by the
inverse of its content, so that its content is 1. A sum whose content is 1
is its own primitive part; only the division of rationals is used. -/
def primitivePart (c : ℚ) (ms : List (ℚ × Term)) : Term :=
  scaleSum (sumContent c ms)⁻¹ c ms

/-- The content of a term: that of a sum, and 1 for any other term. -/
def Term.content : Term → ℚ
  | .sum c ms => sumContent c ms
  | _ => 1

/-- The primitive part of a term: that of a sum, and any other term itself.
A sum that is a factor or a base is taken by its primitive part, and so is
a base of `N`. -/
def Term.primitive : Term → Term
  | .sum c ms => primitivePart c ms
  | t => t

/-! ## Flattening -/

/-- The core of the monomial of a product with the factors `fs`: its only
factor when it has one, and otherwise the product of its factors with the
coefficient 1. -/
def productCore : List Term → Term
  | [f] => f
  | fs => .product 1 fs

/-- The factors of a core: those of a product, and otherwise the core
itself. -/
def Term.coreFactors : Term → List Term
  | .product _ fs => fs
  | t => [t]

/-- The constant and the monomials that the operands of a sum give, in the
order of the operands: a number adds into the constant, a sum adds its
constant and gives its monomials, a product `c · F` gives the monomial
`(c, productCore F)`, and any other term `t` the monomial `(1, t)`. -/
def sumParts : List Term → ℚ × List (ℚ × Term)
  | [] => (0, [])
  | t :: ts =>
    let rest := sumParts ts
    match t with
    | .number q => (q + rest.1, rest.2)
    | .sum c ms => (c + rest.1, ms ++ rest.2)
    | .product c fs => (rest.1, (c, productCore fs) :: rest.2)
    | t => (rest.1, (1, t) :: rest.2)
  termination_by structural ts => ts

/-! ## Merging, cancellation and assembly -/

/-- The order of monomials by their cores. -/
def monomialCmp (o : Orders) (m n : ℚ × Term) : Ordering := Term.cmp o m.2 n.2

/-- The monomials sorted by core, with the coefficients of equal cores
added. -/
def mergeMonomials (o : Orders) (ms : List (ℚ × Term)) : List (ℚ × Term) :=
  mergeAdjacent (fun m n => if m.2 = n.2 then some (m.1 + n.1, m.2) else none)
    (sortBy (monomialCmp o) ms)

/-- The merged monomials without those whose coefficient is 0, and with the
witness monomial `(0, witnessCore bs)` at its place among the cores, where
`bs` are the maximal elements of the bases that the removed monomials hold
with a negative exponent and the remaining cores do not; no witness when
there are none. -/
def cancelMonomials (o : Orders) (ms : List (ℚ × Term)) : List (ℚ × Term) :=
  let rest := ms.filter fun m => decide (m.1 ≠ 0)
  let zero := ms.filter fun m => decide (m.1 = 0)
  match maxBases o (uncovered (Term.negBasesPairs zero) (Term.negBasesPairs rest)) with
  | [] => rest
  | bs => insertBy (monomialCmp o) (0, witnessCore bs) rest

/-- The sum of the constant `c` and the canonical monomials `ms`: the
number `c` without monomials; with the constant 0 and one monomial, that
monomial, its core for the coefficient 1 and otherwise the product of the
coefficient and the factors of the core; otherwise a sum node. -/
def assembleSum (c : ℚ) : List (ℚ × Term) → Term
  | [] => .number c
  | [(a, t)] =>
    if c = 0 then (if a = 1 then t else .product a t.coreFactors) else .sum c [(a, t)]
  | ms => .sum c ms

/-- The canonical sum of the terms `ts` (`Term::sum`), whose order is `o`:
flattened, merged by core, cancelled and assembled. A condition among the
operands fails with `Syntax`. -/
def mkSum (o : Orders) (ts : List Term) : Result Term :=
  if ts.any Term.isCondition then .fault (.syntax none)
  else
    let parts := sumParts ts
    .value (assembleSum parts.1 (cancelMonomials o (mergeMonomials o parts.2)))

end Kalyx.Spec.Terms

end
