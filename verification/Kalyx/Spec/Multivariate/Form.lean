module

public import Kalyx.Spec.Fields.Laws
public import Kalyx.Spec.Multivariate.Orders
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Multivariate polynomials: representation, canonical forms and normalization

A multivariate polynomial is stored as the list of its terms, each the
exponent vector of a monomial with its coefficient, an element of the
coefficient ring (FLD-R01). This module holds, for every coefficient ring
`CoefficientRing P E U` of the specification of the coefficient fields, one
definition of each of these (MVP-R04):

* `MvPoly n E`, the stored form; its leading term, the last one, with its
  monomial and its coefficient, its total degree and whether it is monic
  (MVP-R02);
* `MvPoly.Canonical`, the canonical form under a monomial order, and
  `MvPoly.interpret`, the polynomial of Mathlib in `MvPolynomial (Fin n)`
  that a stored form denotes; `MultivariateRing.model`, the interpretation of
  the polynomials of a ring in the sense of the coefficient fields
  (`Kalyx.Spec.Fields.Model`);
* `MvPoly.normalize` and `MultivariateRing.normalize`, the canonical form of
  a list of terms in any order, with repeated monomials (MVP-R03).

The coefficients are reached only through the methods of the trait: the sum
of two coefficients is `CoefficientRing.add`, and whether a coefficient is
zero is its zero test (`testZero`); the outcome of a method that is not a
value ends the operation and is its result. The storage cost of a polynomial,
the checks of the limits and the work charges are not part of this
specification.
-/

@[expose] public section

namespace Kalyx.Spec.Multivariate

open Kalyx.Spec.Fields (CoefficientRing Model)

/-! ## Polynomials -/

/-- A multivariate polynomial in `n` variables in its stored form: its terms
`c · x^e`, each the pair of the exponent vector `e` of the monomial and the
coefficient `c`, an element of the coefficient ring, in the stored order. The type holds every list,
canonical or not: `MvPoly.Canonical` says which lists are canonical, and the
operations return canonical ones. A polynomial stores neither its
coefficient ring, nor its variables, nor its order; its exponent vectors
have the length `n` of its ring by their type. -/
structure MvPoly (n : ℕ) (E : Type) where
  /-- The terms, each an exponent vector with its coefficient, in the stored
  order. -/
  terms : List (Exponents n × E)
  deriving DecidableEq

namespace MvPoly

variable {n : ℕ} {E : Type}

/-- The zero polynomial, which has no term. -/
def zero : MvPoly n E := ⟨[]⟩

/-- The exponent vectors of the terms, in the stored order. -/
def monomials (a : MvPoly n E) : List (Exponents n) := a.terms.map Prod.fst

/-- The coefficients of the terms, in the stored order. -/
def coefficients (a : MvPoly n E) : List E := a.terms.map Prod.snd

/-- Whether the polynomial has no term. -/
def isZero (a : MvPoly n E) : Bool := a.terms.isEmpty

/-- The leading term (MVP-R02): the last term, which in a canonical form is
the term of the greatest monomial under the order of the ring; none for the
zero polynomial. -/
def leadingTerm (a : MvPoly n E) : Option (Exponents n × E) := a.terms.getLast?

/-- The exponent vector of the leading term, the leading monomial; none for
the zero polynomial. -/
def leadingMonomial (a : MvPoly n E) : Option (Exponents n) := a.leadingTerm.map Prod.fst

/-- The coefficient of the leading term, the leading coefficient; none for the
zero polynomial. -/
def leadingCoefficient (a : MvPoly n E) : Option E := a.leadingTerm.map Prod.snd

/-- The total degree (MVP-R02): the largest total degree of a monomial of the
terms; none for the zero polynomial. -/
def totalDegree (a : MvPoly n E) : Option ℕ := (a.monomials.map Exponents.degree).max?

variable {P : Type} {K : P → Type} [∀ p, CommRing (K p)]

/-- The canonical form of a polynomial over the parent `p` of its coefficient
ring under the order `o`, with the coefficients interpreted by `M`
(FLD-R01): the exponent vectors are strictly increasing under `o`, so the
last term is the leading term and no monomial repeats, and every coefficient
is a canonical element of `p` that does not denote zero. So the zero
polynomial has no term. Over a coefficient ring whose zero test is exact, a
coefficient denotes zero exactly when the zero test finds it zero, the test
by which the operations drop terms. Where the coefficients have unique
canonical forms, so do the polynomials. -/
def Canonical (M : Model P E K) (p : P) (o : OrderKind n) (a : MvPoly n E) : Prop :=
  a.monomials.Pairwise o.Lt ∧
    ∀ c ∈ a.coefficients, (M p).canonical c ∧ (M p).interpret c ≠ 0

/-- The polynomial of Mathlib that a polynomial over the parent `p` denotes
under `M`: the sum of the monomials `c · x^e` of its terms, each exponent
vector the vector of Mathlib that it denotes (`Exponents.toFinsupp`) and
each coefficient interpreted by `M`. The variable at the position `i` is
`MvPolynomial.X i`. -/
noncomputable def interpret (M : Model P E K) (p : P) (a : MvPoly n E) :
    MvPolynomial (Fin n) (K p) :=
  (a.terms.map fun t => MvPolynomial.monomial t.1.toFinsupp ((M p).interpret t.2)).sum

end MvPoly

/-! ## The interpretation of a ring -/

variable {n : ℕ} {P E : Type}

/-- The interpretation of the polynomials of the rings with `n` variables over
the parents `P` in Mathlib: a polynomial of the ring `r` denotes
`MvPoly.interpret` over the parent of its coefficient ring, a polynomial of
`MvPolynomial (Fin n) (K r.coefficients)`, and the canonical polynomials are
those of `MvPoly.Canonical` under the order of `r`. The names of the
variables do not change the interpretation. -/
noncomputable def MultivariateRing.model {K : P → Type} [∀ p, CommRing (K p)]
    (M : Model P E K) :
    Model (MultivariateRing P n) (MvPoly n E) (fun r => MvPolynomial (Fin n) (K r.coefficients)) :=
  fun r => ⟨MvPoly.interpret M r.coefficients, MvPoly.Canonical M r.coefficients r.order⟩

/-- The result `o` is a canonical polynomial of the ring `r` under `M` that
denotes `x`, as `Model.Yields` is for the elements of a coefficient ring. -/
def MultivariateRing.Yields {K : P → Type} [∀ p, CommRing (K p)] (M : Model P E K)
    (r : MultivariateRing P n) (o : MvResult (MvPoly n E))
    (x : MvPolynomial (Fin n) (K r.coefficients)) : Prop :=
  ∃ a, o = .value a ∧ (MultivariateRing.model M r).canonical a ∧
    (MultivariateRing.model M r).interpret a = x

/-! ## Monomials and the monic test -/

/-- The polynomial `c · x^e` of one term, the zero polynomial when the zero
test finds `c` zero. -/
def MvPoly.monomial (R : CoefficientRing P E Empty) (p : P) (e : Exponents n) (c : E) :
    MvResult (MvPoly n E) := do
  if ← testZero R p c then pure .zero else pure ⟨[(e, c)]⟩

/-- Whether the polynomial is monic (MVP-R02): its leading coefficient is 1,
which the zero test of the difference of the leading coefficient and the one
of `p` decides. The zero polynomial has no leading coefficient and is not
monic. Since the leading term is the last term, which the order of the ring
determines, whether a polynomial is monic depends on the order. -/
def MvPoly.isMonic (R : CoefficientRing P E Empty) (p : P) (a : MvPoly n E) : MvResult Bool :=
  match a.leadingCoefficient with
  | none => .value false
  | some c => do testZero R p (← MvResult.ofOutcome (R.subtract p c (R.one p)))

/-! ## Normalization -/

/-- The term `t` inserted into the terms `ts`, whose exponent vectors are
strictly increasing under the order `o`: before the first term whose vector
is above that of `t`, or, where a term has the vector of `t`, in its place
with the sum of its coefficient and that of `t`, by `CoefficientRing.add`.
No coefficient is tested here. -/
def MvPoly.insertTerm (R : CoefficientRing P E Empty) (p : P) (o : OrderKind n)
    (t : Exponents n × E) : List (Exponents n × E) → MvResult (List (Exponents n × E))
  | [] => .value [t]
  | u :: us =>
    match o.compare t.1 u.1 with
    | .lt => .value (t :: u :: us)
    | .eq => do pure ((u.1, ← MvResult.ofOutcome (R.add p u.2 t.2)) :: us)
    | .gt => do pure (u :: (← MvPoly.insertTerm R p o t us))
  termination_by structural us => us

/-- The terms `ts`, each in turn in their order, inserted into the terms
`acc` by `MvPoly.insertTerm`. -/
def MvPoly.insertAll (R : CoefficientRing P E Empty) (p : P) (o : OrderKind n)
    (acc : List (Exponents n × E)) : List (Exponents n × E) → MvResult (List (Exponents n × E))
  | [] => .value acc
  | t :: ts => do MvPoly.insertAll R p o (← MvPoly.insertTerm R p o t acc) ts
  termination_by structural ts => ts

/-- The terms `ts` without those whose coefficient the zero test finds zero,
each tested in turn in their order. -/
def MvPoly.dropZeros (R : CoefficientRing P E Empty) (p : P) :
    List (Exponents n × E) → MvResult (List (Exponents n × E))
  | [] => .value []
  | t :: ts => do
    let vanishes ← testZero R p t.2
    let rest ← MvPoly.dropZeros R p ts
    pure (if vanishes then rest else t :: rest)
  termination_by structural ts => ts

/-- The polynomial of the terms `ts` over the parent `p` under the order `o`
(MVP-R03), the construction of a polynomial from terms: the terms are sorted by `o`, the
coefficients of each monomial are added by the coefficient ring, the terms
inserted in their order (`MvPoly.insertAll`), and then every term whose
coefficient the zero test finds zero is dropped (`MvPoly.dropZeros`). On
canonical coefficients the result is the canonical form of the sum of the
terms, whatever their order. A term here is a pair of an exponent vector and
a coefficient, not a term of the term core. -/
def MvPoly.normalize (R : CoefficientRing P E Empty) (p : P) (o : OrderKind n)
    (ts : List (Exponents n × E)) : MvResult (MvPoly n E) := do
  pure ⟨← MvPoly.dropZeros R p (← MvPoly.insertAll R p o [] ts)⟩

/-- The polynomial of the terms `ts` in the ring `r` (MVP-R03):
`MvPoly.normalize` over the parent of the coefficient ring of `r` under its
order. -/
def MultivariateRing.normalize (R : CoefficientRing P E Empty) (r : MultivariateRing P n)
    (ts : List (Exponents n × E)) : MvResult (MvPoly n E) :=
  MvPoly.normalize R r.coefficients r.order ts

end Kalyx.Spec.Multivariate

end
