module

public import Kalyx.Spec.Terms.Order

/-!
# Terms: negative exponents and witnesses

`N(t)`, the bases of the negative powers of a term, and the witnesses that
keep them where a simplification would lose them (terms contract, "Negative
exponents and witnesses"; architecture, "Negative-exponent invariant",
"Constants"; TRM-R05, TRM-R06):

* `Term.negBases t` lists `N(t)`: the base `b` of every power `b ^ k` with
  `k < 0` in `t`, nested ones included, also inside the arguments of calls
  and the operands of conditions. A constant is never 0 and never an element
  of `N`, so a negative power of a constant adds nothing. A base that is a
  sum is taken as it stands: in a canonical term it is primitive, as the
  constructors hold it. The list may repeat a base; `N(t)` is its set of
  elements.
* `Term.hasNegativePower t` is `N(t)` not empty: so it is false for `π⁻¹`.
  `BasesKept ts t` says that `N` of each of `ts` is contained in `N(t)`.
* `maxBases o bs` keeps the maximal elements of a list of bases, those that
  do not occur with a negative exponent inside another element, sorted in
  the order of terms and without repetitions: the bases that a witness
  names.
* The witnesses: the one `(b⁻¹)⁰` (`Term.oneOf`), the zero witness
  `0 · ∏ b⁻¹` (`zeroWitness`), the core of the witness monomial of a sum
  (`witnessCore`), and the power 0 of a term (`powerZero`), which is 1 or
  the ones of the maximal elements of its `N`.
-/

@[expose] public section

namespace Kalyx.Spec.Terms

/-! ## The bases of negative powers -/

mutual

/-- `N(t)` as a list: the base of every power with a negative exponent in
`t` whose base is not a constant, nested ones included, in the order of a
walk of the tree; a base may occur more than once. -/
def Term.negBases : Term → List Term
  | .number _ | .constant _ | .symbol _ => []
  | .call _ args => Term.negBasesList args
  | .power b k => (if k < 0 ∧ !b.isConstant then [b] else []) ++ Term.negBases b
  | .product _ fs => Term.negBasesList fs
  | .sum _ ms => Term.negBasesPairs ms
  | .condition _ ops => Term.negBasesList ops
  termination_by structural t => t

/-- The bases of the negative powers of a list of terms, those of each term
in order. -/
def Term.negBasesList : List Term → List Term
  | [] => []
  | t :: ts => Term.negBases t ++ Term.negBasesList ts
  termination_by structural ts => ts

/-- The bases of the negative powers of the cores of a list of monomials. -/
def Term.negBasesPairs : List (ℚ × Term) → List Term
  | [] => []
  | (_, t) :: ms => Term.negBases t ++ Term.negBasesPairs ms
  termination_by structural ms => ms

end

/-- Whether a term holds a power with a negative exponent over a base that
is not a constant: `N(t)` is not empty. -/
def Term.hasNegativePower (t : Term) : Bool := !t.negBases.isEmpty

/-- `N` of each of the terms `ts` is contained in `N(t)`: the structural
form of the negative-exponent invariant for the operands `ts` of a
construction and its result `t`, whose bases that are sums are primitive as
the operands of a constructor hold them. -/
def BasesKept (ts : List Term) (t : Term) : Prop := ∀ b ∈ Term.negBasesList ts, b ∈ t.negBases

/-- A list sorted in the order of terms, each term once. -/
def sortedTerms (o : Orders) (ts : List Term) : List Term :=
  mergeAdjacent (fun a b => if a = b then some a else none) (sortBy (Term.cmp o) ts)

/-- The maximal elements of a list of bases: those that do not occur with a
negative exponent inside another element of the list, sorted in the order
of terms and each once. Every element outside them occurs with a negative
exponent inside a maximal one. -/
def maxBases (o : Orders) (bs : List Term) : List Term :=
  sortedTerms o (bs.filter fun b => !bs.any fun c => c.negBases.contains b)

/-- The bases of `bs` that `covered` does not hold. -/
def uncovered (bs covered : List Term) : List Term := bs.filter fun b => !covered.contains b

/-! ## Witnesses -/

/-- The reciprocal `b⁻¹`, the power of `b` with the exponent `-1`. -/
def Term.reciprocal (b : Term) : Term := .power b (-1)

/-- The one `(b⁻¹)⁰`: the power 0 of the reciprocal of `b`, whose value is 1
wherever `b` is not 0, and which keeps `b` in `N`. -/
def Term.oneOf (b : Term) : Term := .power (.power b (-1)) 0

/-- Whether a term is a one `(b⁻¹)⁰`. -/
def Term.isOne : Term → Bool
  | .power (.power _ (-1)) 0 => true
  | _ => false

/-- The zero witness of the bases `bs`, given as the maximal elements in
order: `0 · ∏ b⁻¹`, a product with the coefficient 0 whose factors are the
reciprocals, and the number 0 when there are no bases. -/
def zeroWitness (bs : List Term) : Term :=
  if bs.isEmpty then .number 0 else .product 0 (bs.map Term.reciprocal)

/-- The core of the witness monomial of a sum over the bases `bs`, given as
the maximal elements in order: the reciprocal `b⁻¹` for one base, and the
product of the reciprocals with the coefficient 1 otherwise. -/
def witnessCore : List Term → Term
  | [b] => b.reciprocal
  | bs => .product 1 (bs.map Term.reciprocal)

/-- The power 0 of a term `t` that is not a number (rule 4 of powers): the
number 1 when `N(t)` is empty, and otherwise the ones `(b⁻¹)⁰` of the maximal
elements `b` of `N(t)`: the one itself for a single element, and the
product of the ones with the coefficient 1 otherwise. A constant is not in
`N`, so `c⁰ = 1` for a constant `c`. -/
def powerZero (o : Orders) (t : Term) : Term :=
  match maxBases o t.negBases with
  | [] => .number 1
  | [b] => b.oneOf
  | bs => .product 1 (bs.map Term.oneOf)

end Kalyx.Spec.Terms

end
