module

public import Kalyx.Spec.Fields.Laws
public import Kalyx.Spec.Terms.Basic
public import Mathlib.Algebra.Polynomial.Basic

/-!
# Polynomials: representation, canonical forms and results

The specification of the univariate polynomials of kalyx (the ring `K[x]` of
one variable over a coefficient ring `K`, its polynomials, their storage cost
and limits, the ring operations, the shared algorithms, and over `ℚ` the
expansion of terms, the conversion back to terms and differentiation) is
written from the requirements of the polynomials contract
(`docs/components/polynomials/contract.md`) and from the design rules of the
coefficient-field trait in the architecture (`docs/architecture.md`), not
from the implementation. The coefficients are reached only through the
methods of the trait as the specification of the coefficient fields states it
(`Kalyx.Spec.Fields.CoefficientRing`), which every operation takes as a
parameter (POL-R10); this specification does not restate the coefficient
rings. This module holds what all the parts share:

* `Poly`, a polynomial as the library stores it, the list of its terms, each
  a degree with its coefficient; its degree and leading coefficient;
  `Poly.Canonical`, the canonical form (FLD-R01); and `Poly.interpret`, the
  polynomial of Mathlib that it denotes;
* `PolynomialRing`, the parent: the parent of the coefficient ring and the
  name of the variable; and `PolynomialRing.model`, the interpretation of its
  polynomials in Mathlib's `Polynomial`, an interpretation in the sense of the
  coefficient fields (`Kalyx.Spec.Fields.Model`);
* `PolyFault` and `PolyResult`, the faults and the results of the operations,
  with the lifts of the outcomes of the coefficient fields and of the results
  of the term core;
* the zero test of a coefficient as the operations use it (FLD-R04), and the
  one writer of the terms.

The limits that an operation reads are explicit parameters (`Limits`, in
`Kalyx.Spec.Polynomials.Storage`), not a request context. Work charges,
cancellation and deadlines are not part of this specification.
-/

@[expose] public section

namespace Kalyx.Spec.Polynomials

open Kalyx.Spec.Fields (CoefficientRing Model FieldError LimitField Outcome)
open Kalyx.Spec.Terms (TermFault)

/-! ## Polynomials -/

/-- A polynomial as the library stores it, kalyx's `Polynomial<K>`: its terms
`c x^d`, each the pair of the degree `d` and the coefficient `c`, an element of
the coefficient ring, in the stored order. The contract keeps the degrees and
the coefficients in two lists of the same length; the pairs hold the same
data. The type holds every list, canonical or not: `Poly.Canonical` says
which lists are canonical, and the operations return canonical ones. A
polynomial stores neither its coefficient ring nor its variable. Degrees are
natural numbers: the limits keep every degree of a result below `2⁶³`, and
the width of `u64` is not part of this specification. -/
structure Poly (E : Type) where
  /-- The terms, each a degree with its coefficient, in the stored order. -/
  terms : List (ℕ × E)
  deriving DecidableEq, Repr

namespace Poly

variable {E : Type}

/-- The zero polynomial, which has no term. -/
def zero : Poly E := ⟨[]⟩

/-- The degrees of the terms, kalyx's `degrees()`. -/
def degrees (a : Poly E) : List ℕ := a.terms.map Prod.fst

/-- The coefficients of the terms, kalyx's `coefficients()`. -/
def coefficients (a : Poly E) : List E := a.terms.map Prod.snd

/-- Whether the polynomial has no term, kalyx's `is_zero()`. -/
def isZero (a : Poly E) : Bool := a.terms.isEmpty

/-- The degree, kalyx's `degree()`: the degree of the last term, none for the
zero polynomial. -/
def degree (a : Poly E) : Option ℕ := a.terms.getLast?.map Prod.fst

/-- The leading coefficient: the coefficient of the last term, none for the
zero polynomial. -/
def leadingCoefficient (a : Poly E) : Option E := a.terms.getLast?.map Prod.snd

variable {P : Type} {K : P → Type} [∀ p, CommRing (K p)]

/-- The canonical form of a polynomial over the parent `p` of its coefficient
ring, under the interpretation `M` of the coefficients (FLD-R01): the degrees
are strictly increasing, and every coefficient is a canonical element of `p`
that does not denote zero. So the zero polynomial has no term, and the last
degree is the degree. Over a coefficient ring whose zero test is exact, a
coefficient denotes zero exactly when the zero test finds it zero, the test
by which the operations drop terms (FLD-R04). Where the coefficients have
unique canonical forms, so do the polynomials. -/
def Canonical (M : Model P E K) (p : P) (a : Poly E) : Prop :=
  a.degrees.Pairwise (· < ·) ∧
    ∀ c ∈ a.coefficients, (M p).canonical c ∧ (M p).interpret c ≠ 0

/-- The polynomial of Mathlib that a polynomial over the parent `p` denotes
under `M`: the sum of the monomials `c x^d` of its terms, each coefficient
interpreted by `M`. The variable is the generator `X`. -/
noncomputable def interpret (M : Model P E K) (p : P) (a : Poly E) : Polynomial (K p) :=
  (a.terms.map fun t => Polynomial.monomial t.1 ((M p).interpret t.2)).sum

end Poly

/-! ## The ring -/

/-- The parent of the polynomials, kalyx's `PolynomialRing<K>`: the parent of
the coefficient ring and the name of the variable. The operations take the
ring and assume that the polynomials they are given belong to it, built by it
or by a ring with the same coefficient ring and variable; they never compare
rings (polynomials contract, "The two types and the receiver rule"). The name
is checked when a ring is built from a request, with the rule of symbol names
of the term core (POL-R01); this structure holds any name. -/
structure PolynomialRing (P : Type) where
  /-- The parent of the coefficient ring, kalyx's `coefficient_ring()`. -/
  coefficients : P
  /-- The name of the variable, kalyx's `variable()`. -/
  variableName : String
  deriving DecidableEq, Repr

/-- The interpretation of the polynomials of the rings over the parents `P`
in Mathlib: a polynomial of the ring `r` denotes `Poly.interpret` over the
parent of its coefficient ring, a polynomial over the commutative ring
`K r.coefficients`, and the canonical polynomials are those of
`Poly.Canonical`. The name of the variable does not change the
interpretation. -/
noncomputable def PolynomialRing.model {P E : Type} {K : P → Type} [∀ p, CommRing (K p)]
    (M : Model P E K) :
    Model (PolynomialRing P) (Poly E) (fun r => Polynomial (K r.coefficients)) :=
  fun r => ⟨Poly.interpret M r.coefficients, Poly.Canonical M r.coefficients⟩

/-! ## Faults and results -/

/-- The faults that the polynomials report, a part of the fault kinds of
kalyx: those of the coefficient fields (`FieldError`), such as
`DivisionByZero` of a division by the zero polynomial and the faults of a
coefficient operation; those of the term core (`TermFault`), such as `Syntax`
and `Unsupported` of the name of a variable, `UnknownSymbol` of the expansion
and `Internal`; and `NotPolynomial`, of a term that the expansion cannot take
into a polynomial. `DivisionByZero` and `OutsideDomain`, which both
enumerations name, are always given as faults of the coefficient fields
(`PolyFault.ofTermFault`), so that each fault of kalyx has one form. -/
inductive PolyFault where
  /-- A fault of the coefficient fields. -/
  | field (kind : FieldError)
  /-- A fault of the term core. -/
  | term (kind : TermFault)
  /-- `NotPolynomial`. -/
  | notPolynomial
  deriving DecidableEq, Repr

/-- The fault of the polynomials for a fault of the term core:
`DivisionByZero` and `OutsideDomain` as faults of the coefficient fields, the
others as faults of the term core. -/
def PolyFault.ofTermFault : TermFault → PolyFault
  | .divisionByZero => .field .divisionByZero
  | .outsideDomain => .field .outsideDomain
  | k => .term k

/-- The result of an operation of the polynomials: a value, a fault, or
`ResourceLimit` naming the field of the limits that a check found exceeded.
The failures of a request context (exhausted work, cancellation, an expired
deadline) are not results of this specification. -/
inductive PolyResult (α : Type) where
  /-- The operation returns the value `v`. -/
  | value (v : α)
  /-- The operation fails with the fault `kind`. -/
  | fault (kind : PolyFault)
  /-- The operation fails with `ResourceLimit` naming `field`. -/
  | resourceLimit (field : LimitField)
  deriving DecidableEq, Repr

/-- The result with `f` applied to its value; faults and limits are kept. -/
def PolyResult.map {α β : Type} (f : α → β) : PolyResult α → PolyResult β
  | .value v => .value (f v)
  | .fault e => .fault e
  | .resourceLimit l => .resourceLimit l

/-- The result of `f` on the value of a result; a fault or a limit stops the
operation and is its result. -/
def PolyResult.bind {α β : Type} : PolyResult α → (α → PolyResult β) → PolyResult β
  | .value v, f => f v
  | .fault e, _ => .fault e
  | .resourceLimit l, _ => .resourceLimit l

instance : Monad PolyResult where
  pure := .value
  map := PolyResult.map
  bind := PolyResult.bind

/-- The outcome of an operation of the coefficient fields as a result: the
value, the fault as a fault of the coefficient fields, or the same limit. -/
def PolyResult.ofOutcome {α : Type} : Outcome α → PolyResult α
  | .value v => .value v
  | .fault e => .fault (.field e)
  | .resourceLimit l => .resourceLimit l

/-- The result of a construction of the term core as a result: the value, the
fault by `PolyFault.ofTermFault`, or the same limit. -/
def PolyResult.ofResult {α : Type} : Terms.Result α → PolyResult α
  | .value v => .value v
  | .fault e => .fault (PolyFault.ofTermFault e)
  | .resourceLimit l => .resourceLimit l

/-- The result `o` is a canonical polynomial over the parent `p` under `M`
that denotes `x`, as `Model.Yields` is for elements; for a polynomial of the
ring `r`, the parent is `r.coefficients`. -/
def Poly.Yields {P E : Type} {K : P → Type} [∀ p, CommRing (K p)] (M : Model P E K) (p : P)
    (o : PolyResult (Poly E)) (x : Polynomial (K p)) : Prop :=
  ∃ a, o = .value a ∧ a.Canonical M p ∧ a.interpret M p = x

/-! ## Zero tests and the writer

The operations take only a coefficient ring whose zero test always decides
(FLD-R04): one whose reason type of an undecided test is `Empty`, which has
no value, as for the rationals and the prime fields. They rely on the zero
test to drop every term whose coefficient is zero. -/

variable {P E : Type}

/-- The zero test of the coefficient `c` of the parent `p`, as the operations
use it: `true` for zero and `false` for nonzero. An undecided answer cannot
arise, and a fault or a limit of the test ends the operation. -/
def testZero (R : CoefficientRing P E Empty) (p : P) (c : E) : PolyResult Bool :=
  PolyResult.ofOutcome <| (R.zeroTest p c).map fun
    | .zero => true
    | .nonzero => false
    | .undecided u => nomatch u

/-- The one writer of the terms (polynomials contract, "Representation and
invariants"): the term `c x^d` appended above the last degree. A term at or
below the last degree breaks the invariant and is `Internal`, with nothing
appended; on canonical operands the operations never reach it. The writer
does not test the coefficient. -/
def Poly.append (a : Poly E) (d : ℕ) (c : E) : PolyResult (Poly E) :=
  if a.degree.all (· < d) then .value ⟨a.terms ++ [(d, c)]⟩ else .fault (.term .internal)

/-- A term written after its zero test, as the operations write every term
whose coefficient they computed: `a` unchanged when the zero test finds `c`
zero, and otherwise `c x^d` appended by the writer. -/
def Poly.appendNonzero (R : CoefficientRing P E Empty) (p : P) (a : Poly E) (d : ℕ) (c : E) :
    PolyResult (Poly E) := do
  if ← testZero R p c then pure a else a.append d c

/-- The polynomial `c x^d` of one term, the zero polynomial when the zero test
finds `c` zero, as one, the variable and the constants are built. -/
def Poly.monomial (R : CoefficientRing P E Empty) (p : P) (d : ℕ) (c : E) : PolyResult (Poly E) :=
  Poly.zero.appendNonzero R p d c

end Kalyx.Spec.Polynomials

end
