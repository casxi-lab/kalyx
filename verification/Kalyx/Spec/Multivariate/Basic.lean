module

public import Kalyx.Spec.Fields.Laws
public import Kalyx.Spec.Terms.Basic
public import Kalyx.Spec.Terms.Call
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finsupp.Fintype

/-!
# Multivariate polynomials: monomials, rings and results

The specification of the multivariate polynomials of kalyx (the ring
`K[x₁, …, xₙ]` of finitely many variables over a coefficient ring `K` with a
monomial order, its polynomials, the ring operations, and over `ℚ` the
expansion of terms and the conversion back to terms) is written from the
requirements of the multivariate contract
(`docs/components/multivariate/contract.md`) and from the design rules of the
coefficient-field trait in the architecture (`docs/architecture.md`), not
from the implementation. The coefficients are reached only through the
methods of the trait as the specification of the coefficient fields states it
(`Kalyx.Spec.Fields.CoefficientRing`), which every operation takes as a
parameter (MVP-R04). This module holds what all the parts share:

* `Exponents n`, the exponent vector of a monomial in `n` variables, with the
  product of monomials, the total degree and the vector of Mathlib that it
  denotes (FLD-R06);
* `OrderKind n`, the monomial orders of a ring: `lex`, `grlex`, `grevlex`
  and the block orders, whose split is at most `n` by its type (FLD-R06);
* `MultivariateRing`, the parent: the parent of the coefficient ring, the
  ordered names of the variables and the monomial order; its construction and
  its identity (MVP-R01);
* `MvFault` and `MvResult`, the faults and the results of the operations,
  with the lifts of the outcomes of the coefficient fields and of the results
  of the term core, and the zero test of a coefficient as the operations use
  it.

The operations read no limits: the checks of the limits, the storage cost
and the work charges of the multivariate polynomials are not part of this
specification, and every operation is given as a total function of its
operands apart from the outcomes of the coefficient methods and of the
constructors of the term core, which it passes on. Cancellation and
deadlines are not part of it either.
-/

@[expose] public section

namespace Kalyx.Spec.Multivariate

open Kalyx.Spec.Fields (CoefficientRing FieldError LimitField Outcome)
open Kalyx.Spec.Terms (TermFault mkSymbol)

/-! ## Exponent vectors

A monomial `x₁^e₁ ⋯ xₙ^eₙ` of a ring with `n` variables is its exponent
vector `(e₁, …, eₙ)`, the exponent of the variable at the position `i`, from
0, at `i`; the first variable is the most significant. A vector is the
function `Fin n → ℕ`: its length is `n` by its type, so a vector of another
length cannot arise; it is computable, with a decidable equality, a vector of
three variables is written `![2, 0, 1]`, and it denotes a vector of Mathlib,
`Fin n →₀ ℕ`, through the bijection `Finsupp.equivFunOnFinite`. The pointwise
order of Mathlib on functions is not a monomial order and is never used
here; the monomial orders are those of `Kalyx.Spec.Multivariate.Orders`. -/

/-- The exponent vector of a monomial in `n` variables: the exponent of each
variable, by its position. -/
abbrev Exponents (n : ℕ) : Type := Fin n → ℕ

namespace Exponents

variable {n : ℕ}

/-- The vector of the constant monomial `1`, whose exponents are all 0. -/
def constant : Exponents n := fun _ => 0

/-- The vector of the variable at the position `i`: the exponent 1 at `i`
and 0 elsewhere. -/
def generator (i : Fin n) : Exponents n := fun j => if j = i then 1 else 0

/-- The product of two monomials, the sum of their exponent vectors
(FLD-R06). -/
def product (a b : Exponents n) : Exponents n := fun i => a i + b i

/-- The total degree of a monomial, the sum of its exponents. -/
def degree (a : Exponents n) : ℕ := ∑ i, a i

/-- The vector of Mathlib that an exponent vector denotes, the same exponents
as a finitely supported function. -/
noncomputable def toFinsupp (a : Exponents n) : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm a

end Exponents

/-! ## Monomial orders -/

/-- The monomial order of a ring with `n` variables, kalyx's `MonomialOrder`
(FLD-R06): `lex`, `grlex` (`GradedLex`), `grevlex` (`GradedReverseLex`), or
the block order `block k` of the split `k`, whose first block is the first
`k` variables and whose second block is the last `n - k`, each block ordered
by `grevlex`. The split is an element of `Fin (n + 1)`, so it is at most the
number of variables by its type, and a split above it cannot arise. The
comparisons are those of `Kalyx.Spec.Multivariate.Orders`. -/
inductive OrderKind (n : ℕ) where
  /-- `lex`: the exponents are compared from the first variable. -/
  | lex
  /-- `grlex`: the total degree first, then as `lex`. -/
  | grlex
  /-- `grevlex`: the total degree first, then the smaller exponent at the last
  variable where the exponents differ belongs to the greater monomial. -/
  | grevlex
  /-- `block k`: the first `k` variables by `grevlex`, then on a tie the last
  `n - k` variables by `grevlex`. -/
  | block (k : Fin (n + 1))
  deriving DecidableEq, Repr

/-! ## Faults and results -/

/-- The faults that the multivariate polynomials report, a part of the fault
kinds of kalyx: those of the coefficient fields (`FieldError`), the faults of
a coefficient method; those of the term core (`TermFault`), such as `Syntax`
and `Unsupported` of the name of a variable, `UnknownSymbol` of the expansion
and `Internal`; and `NotPolynomial`, of a term that the expansion cannot take
into a polynomial. `DivisionByZero` and `OutsideDomain`, which both
enumerations name, are always given as faults of the coefficient fields
(`MvFault.ofTermFault`), so that each fault of kalyx has one form. -/
inductive MvFault where
  /-- A fault of the coefficient fields. -/
  | field (kind : FieldError)
  /-- A fault of the term core. -/
  | term (kind : TermFault)
  /-- `NotPolynomial`. -/
  | notPolynomial
  deriving DecidableEq, Repr

/-- The fault of the multivariate polynomials for a fault of the term core:
`DivisionByZero` and `OutsideDomain` as faults of the coefficient fields, the
others as faults of the term core. -/
def MvFault.ofTermFault : TermFault → MvFault
  | .divisionByZero => .field .divisionByZero
  | .outsideDomain => .field .outsideDomain
  | k => .term k

/-- The result of an operation of the multivariate polynomials: a value, a
fault, or `ResourceLimit` naming the field of the limits, which only a
coefficient method or a constructor of the term core reports here, since the
operations of this specification check no limits of their own. -/
inductive MvResult (α : Type) where
  /-- The operation returns the value `v`. -/
  | value (v : α)
  /-- The operation fails with the fault `kind`. -/
  | fault (kind : MvFault)
  /-- The operation fails with `ResourceLimit` naming `field`. -/
  | resourceLimit (field : LimitField)
  deriving DecidableEq, Repr

/-- The result with `f` applied to its value; faults and limits are kept. -/
def MvResult.map {α β : Type} (f : α → β) : MvResult α → MvResult β
  | .value v => .value (f v)
  | .fault e => .fault e
  | .resourceLimit l => .resourceLimit l

/-- The result of `f` on the value of a result; a fault or a limit stops the
operation and is its result. -/
def MvResult.bind {α β : Type} : MvResult α → (α → MvResult β) → MvResult β
  | .value v, f => f v
  | .fault e, _ => .fault e
  | .resourceLimit l, _ => .resourceLimit l

instance : Monad MvResult where
  pure := .value
  map := MvResult.map
  bind := MvResult.bind

/-- The outcome of a method of the coefficient fields as a result: the value,
the fault as a fault of the coefficient fields, or the same limit. -/
def MvResult.ofOutcome {α : Type} : Outcome α → MvResult α
  | .value v => .value v
  | .fault e => .fault (.field e)
  | .resourceLimit l => .resourceLimit l

/-- The result of a construction of the term core as a result: the value, the
fault by `MvFault.ofTermFault`, or the same limit. -/
def MvResult.ofResult {α : Type} : Terms.Result α → MvResult α
  | .value v => .value v
  | .fault e => .fault (MvFault.ofTermFault e)
  | .resourceLimit l => .resourceLimit l

/-! ## Zero tests

The operations take only a coefficient ring whose zero test always decides:
one whose reason type of an undecided test is `Empty`, which has no value, as
for the rationals and the prime fields. They rely on the zero test to drop
every term whose coefficient is zero. -/

/-- The zero test of the coefficient `c` of the parent `p`, as the operations
use it: `true` for zero and `false` for nonzero. An undecided answer cannot
arise, and a fault or a limit of the test ends the operation. -/
def testZero {P E : Type} (R : CoefficientRing P E Empty) (p : P) (c : E) : MvResult Bool :=
  MvResult.ofOutcome <| (R.zeroTest p c).map fun
    | .zero => true
    | .nonzero => false
    | .undecided u => nomatch u

/-! ## The ring -/

/-- The parent of the multivariate polynomials in `n` variables, kalyx's
`MultivariateRing<K>` (MVP-R01): the parent of the coefficient ring, the
names of the variables in their order, the first variable the most
significant, and the monomial order. The operations take the ring as their
receiver and assume that the polynomials they are given belong to it, built
by it or by an equal ring; they never compare rings. Two rings are the same
exactly when they are equal: the same parent of the coefficient ring, the
same names in the same order and the same order, a block order with its
split. So rings with the same variables in another order are different, and
so are the block orders `block 0` and `block n` and `grevlex`, which order
the monomials alike. The structure holds any names; `MultivariateRing.new`
builds the rings whose names are valid. -/
structure MultivariateRing (P : Type) (n : ℕ) where
  /-- The parent of the coefficient ring. -/
  coefficients : P
  /-- The names of the variables, in their order. -/
  variableNames : List String
  /-- There is one name for each variable. -/
  length_variableNames : variableNames.length = n
  /-- The monomial order. -/
  order : OrderKind n
  deriving DecidableEq

/-- The check of the names of the variables of a ring, each in turn in their
order, after the names `seen` before it: a name that is not a symbol name
fails as the symbol constructor `mkSymbol` fails, with `Syntax` and the span
of its first character that the form does not allow, the empty span at 0 for
the empty name, or with `Unsupported` and the span of the whole name for a
reserved name; then a name equal to an earlier one fails with `Syntax`
without a span. Names are compared byte by byte, so they are
case-sensitive. -/
def checkVariableNames (seen : List String) : List String → MvResult Unit
  | [] => .value ()
  | name :: names => do
    let _ ← MvResult.ofResult (mkSymbol name)
    if name ∈ seen then .fault (.term (.syntax none))
    else checkVariableNames (name :: seen) names
  termination_by structural names => names

/-- `MultivariateRing::new` (MVP-R01): the ring over the parent `coefficients`
with the variables `names`, in their order, and the monomial order `order`,
when the names are valid (`checkVariableNames`): each a symbol name, no two
equal. The list of names may be empty, which is the ring without variables,
whose only monomial is the constant one. The split of a block order is at
most the number of names by its type. -/
def MultivariateRing.new {P : Type} (coefficients : P) (names : List String)
    (order : OrderKind names.length) : MvResult (MultivariateRing P names.length) := do
  checkVariableNames [] names
  pure ⟨coefficients, names, rfl, order⟩

end Kalyx.Spec.Multivariate

end
