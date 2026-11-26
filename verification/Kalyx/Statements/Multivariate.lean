module

public import Kalyx.Spec.Multivariate.Terms
public import Kalyx.Spec.Fields.PrimeField
public import Kalyx.Spec.Terms.Semantics
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder

/-!
# Statements about the multivariate polynomials

The registered statements of the specification of the multivariate
polynomials (`Kalyx.Spec.Multivariate`), each a proposition named here and
proved, or to be proved, by a theorem of `Kalyx.Proofs.Multivariate`. They
are written from the numbered requirements of the multivariate contract
(`docs/components/multivariate/contract.md`), whose table of requirements and
statements names, for each requirement, the statements that state it.

The first ten are the properties. Six are about the monomial orders, for
every number of variables and every order, the block orders with every split
up to the number of variables among them: each is a strict total order with
which its computable comparison agrees, compatible with the product of
monomials, well founded, with the constant monomial least; a block order
eliminates its first block and orders the monomials as `grevlex` for the
splits 0 and `n`; and each is the strict order of a monomial order of
Mathlib. This specification builds no monomial order of Mathlib: one statement
says that such an order exists, and the statement about leading terms holds
for every monomial order of Mathlib that agrees with the order of the ring.
The others are about the polynomials: canonical forms are unique and the ring
operations are exact under the interpretation in Mathlib's
`MvPolynomial (Fin n)`; the leading term, the total degree and the monic
test are those of Mathlib; normalization gives the canonical form of the sum
of its terms, whatever their order; and expansion and the conversion back to
terms keep the meaning of terms. A property of the polynomials holds for every
coefficient ring of the specification of the coefficient fields that is exact
under an interpretation (`ExactRing`): its ring laws hold and its zero test is
exact, as they do for the rationals and the prime fields. The meaning of an
expansion is stated under every interpretation of the calls, conditions and
constants of terms, and that of the conversion back to terms under every
total choice of the orders of the term core (`Orders.Total`) and every lawful
interpretation (`Interp.Lawful`), the parameters of the statements about the
term core.

The remaining twenty are a positive and a negative example of each
requirement. The examples fix the parameters of the conversion back to terms: the order
`Orders.sample` and the limit `defaultMaxExponent`. A ring is written out with
its data, such as `ℚ[x, y, z]` under `lex` (`ratRingXYZ .lex`); a polynomial
over `ℚ` as the list of its terms (`ratPoly`), and over a prime field as the
list of its residues (`residuePoly`); a prime field `𝔽_p` is the one that the
constructor builds from `p`, as in `∃ F, PrimeField.new 5 = .built F ∧ …`. A
term is written as its canonical term, the term that the term core builds
from the input, as a parse of the input text builds it. Where the exponent
vectors of a result are computed, by a product of monomials or as a variable,
the example compares the terms of the result with each exponent vector listed
(`listedTerms`), which determine the polynomial.
-/

@[expose] public section

namespace Kalyx.Statements.Multivariate

open Kalyx.Spec.Fields
open Kalyx.Spec.Multivariate
open Kalyx.Spec.Terms (Term Orders Interp Assignment defaultMaxExponent)

/-! ## Notions of the statements -/

/-- The coefficient ring `R` is exact under the interpretation `M`: its ring
laws hold and its zero test is exact. -/
def ExactRing {P E : Type} {K : P → Type} [∀ p, CommRing (K p)]
    (R : CoefficientRing P E Empty) (M : Model P E K) : Prop :=
  RingLaws R M ∧ ZeroTestExact R M

/-- The value of the polynomial `a` of the ring `r` over `ℚ` at the
assignment `ρ`: the polynomial of Mathlib that `a` denotes, with its rational
coefficients taken into the complex numbers, at the values in `ρ` of the
names of the variables. -/
noncomputable def polyValue {n : ℕ} (r : MultivariateRing Rationals n) (a : MvPoly n Fraction)
    (ρ : Assignment) : ℂ :=
  (a.interpret Rationals.model r.coefficients).eval₂ (Rat.castHom ℂ) fun i =>
    ρ (r.variableName i)

/-- The terms `(e, c)` of `l` over `ℚ`, each coefficient the reduced fraction
of `c`. -/
def ratTerms {n : ℕ} (l : List (Exponents n × ℚ)) : List (Exponents n × Fraction) :=
  l.map fun t => (t.1, Fraction.ofRat t.2)

/-- The polynomial over `ℚ` with the terms `(e, c)` of `l`, in their order. -/
def ratPoly {n : ℕ} (l : List (Exponents n × ℚ)) : MvPoly n Fraction := ⟨ratTerms l⟩

/-- The terms `(e, c)` of `l` over a prime field, each coefficient the
residue `c`. -/
def residueTerms {n : ℕ} (l : List (Exponents n × ℕ)) : List (Exponents n × PrimeResidue) :=
  l.map fun t => (t.1, ⟨t.2⟩)

/-- The polynomial over a prime field with the terms `(e, c)` of `l`. -/
def residuePoly {n : ℕ} (l : List (Exponents n × ℕ)) : MvPoly n PrimeResidue :=
  ⟨residueTerms l⟩

/-- The terms of a polynomial, each exponent vector written as the list of its
exponents in the order of the variables. A vector is determined by its list,
so two polynomials with the same listed terms are equal. -/
def listedTerms {n : ℕ} {E : Type} (a : MvPoly n E) : List (List ℕ × E) :=
  a.terms.map fun t => (List.ofFn t.1, t.2)

/-- The ring `ℚ[x, y]` under the order `o`. -/
def ratRingXY (o : OrderKind 2) : MultivariateRing Rationals 2 := ⟨⟨⟩, ["x", "y"], rfl, o⟩

/-- The ring `ℚ[x, y, z]` under the order `o`. -/
def ratRingXYZ (o : OrderKind 3) : MultivariateRing Rationals 3 :=
  ⟨⟨⟩, ["x", "y", "z"], rfl, o⟩

/-! ## Properties -/

/-- The monomial orders are strict total orders (FLD-R06): for every number of
variables `n` and every order of a ring with `n` variables, the block orders
of every split up to `n` among them, the strict order is irreflexive,
transitive and trichotomous, and the computable comparison agrees with it: it
is `lt` exactly when the first vector is below the second, `eq` exactly for
equal vectors, and `gt` exactly when the first vector is above the second. -/
def MonomialOrdersAreStrictTotalOrders : Prop :=
  ∀ (n : ℕ) (o : OrderKind n),
    (∀ a, ¬o.Lt a a) ∧ (∀ a b c, o.Lt a b → o.Lt b c → o.Lt a c) ∧
    (∀ a b, o.Lt a b ∨ a = b ∨ o.Lt b a) ∧
    ∀ a b, (o.compare a b = .lt ↔ o.Lt a b) ∧ (o.compare a b = .eq ↔ a = b) ∧
      (o.compare a b = .gt ↔ o.Lt b a)

/-- The monomial orders are compatible with the product of monomials
(FLD-R06): the exponent vector of the product of two monomials, the sum of
their exponent vectors, denotes the sum of the vectors of Mathlib that theirs
denote, the vector of the product of the monomials of Mathlib; and under every
order `a` is below `b` exactly when `a · c` is below `b · c`, so a product
keeps the order and can be cancelled. -/
def MonomialOrdersRespectProducts : Prop :=
  (∀ (n : ℕ) (a b : Exponents n), (a.product b).toFinsupp = a.toFinsupp + b.toFinsupp) ∧
  ∀ (n : ℕ) (o : OrderKind n) (a b c : Exponents n),
    o.Lt a b ↔ o.Lt (a.product c) (b.product c)

/-- The monomial orders are well founded (FLD-R06): no order has an infinite
descending chain. -/
def MonomialOrdersAreWellFounded : Prop :=
  ∀ (n : ℕ) (o : OrderKind n), WellFounded o.Lt

/-- The constant monomial is the least (FLD-R06): under every order, no
vector is below the zero vector, and every other vector is above it. -/
def TheConstantMonomialIsLeast : Prop :=
  ∀ (n : ℕ) (o : OrderKind n), (∀ a, ¬o.Lt a Exponents.constant) ∧
    ∀ a, a ≠ Exponents.constant → o.Lt Exponents.constant a

/-- The block orders eliminate their first block (FLD-R06): under the block
order of the split `k`, `a` is below `b` exactly when the first `k` variables
of `a` are below those of `b` under `grevlex`, or they are equal and the last
`n - k` variables of `a` are below those of `b` under `grevlex`; a monomial
with a positive exponent at one of the first `k` variables is above every
monomial of the last `n - k` variables alone; and the block orders of the
splits 0 and `n` compare monomials as `grevlex` does. -/
def BlockOrdersEliminateTheirFirstBlock : Prop :=
  (∀ (n : ℕ) (k : Fin (n + 1)) (a b : Exponents n),
    ((OrderKind.block k).Lt a b ↔
      GrevLexLT (a.firstBlock k) (b.firstBlock k) ∨
        a.firstBlock k = b.firstBlock k ∧ GrevLexLT (a.secondBlock k) (b.secondBlock k)) ∧
    ((∃ i : Fin n, i.val < k.val ∧ a i ≠ 0) → (∀ i : Fin n, i.val < k.val → b i = 0) →
      (OrderKind.block k).Lt b a)) ∧
  ∀ n : ℕ, (OrderKind.block 0 : OrderKind n).compare = OrderKind.grevlex.compare ∧
    (OrderKind.block (Fin.last n) : OrderKind n).compare = OrderKind.grevlex.compare

/-- The monomial orders are monomial orders of Mathlib (FLD-R06): for every
number of variables `n` and every order, there is a monomial order of Mathlib
on the variables `Fin n` whose strict order, through the vectors of Mathlib
that the exponent vectors denote, is the strict order of the order
(`OrderKind.Agrees`), and so the strict order that its comparison gives. -/
def MonomialOrdersAreThoseOfMathlib : Prop :=
  ∀ (n : ℕ) (o : OrderKind n), ∃ m : MonomialOrder.{0, 0} (Fin n),
    o.Agrees m ∧ ∀ a b : Exponents n,
      m.toSyn a.toFinsupp < m.toSyn b.toFinsupp ↔ o.compare a b = .lt

/-- The ring operations are exact (FLD-R01, FLD-R03, MVP-R04, MVP-R05), over
every coefficient ring `R` whose zero test always decides and that is exact
under the interpretation `M` (`ExactRing`), in every ring `r` with any number
of variables `n`:

* canonical forms are unique: two canonical polynomials of `r` that denote
  the same polynomial of Mathlib are equal; and when every element of the
  coefficient ring has a canonical form, so does every polynomial of Mathlib;
* a polynomial is canonical exactly when its exponent vectors are strictly
  increasing under the order of `r` and each coefficient is canonical and
  nonzero by the zero test, so the zero polynomial has no term;
* the zero polynomial, `one`, `generator`, `constant`, `negate`, `add`,
  `subtract`, `multiply` and `power` of `r` return, on canonical operands, a
  canonical polynomial that denotes `0`, `1`, the variable `Xᵢ`, the constant
  `C c`, the negation, the sum, the difference, the product and the power
  `Aᵏ` in `MvPolynomial (Fin n) (K p)`; no fault and no limit is possible;
* `a⁰` is the polynomial one for every `a`, `0⁰` included, and `0ᵏ` for
  `k ≥ 1` is the zero polynomial. -/
def RingOperationsAreExact : Prop :=
  ∀ (P E : Type) (K : P → Type) [∀ p, CommRing (K p)] (R : CoefficientRing P E Empty)
    (M : Model P E K), ExactRing R M → ∀ (n : ℕ) (r : MultivariateRing P n),
      let p := r.coefficients
      let Q := MultivariateRing.model M r
      Q.Unique ∧ ((M p).Complete → Q.Complete) ∧
      (∀ a, Q.canonical a ↔ a.monomials.Pairwise r.order.Lt ∧
        ∀ c ∈ a.coefficients, (M p).canonical c ∧ R.zeroTest p c = .value .nonzero) ∧
      r.Yields M (.value MvPoly.zero) 0 ∧ r.Yields M (r.one R) 1 ∧
      (∀ i, r.Yields M (r.generator R i) (MvPolynomial.X i)) ∧
      (∀ c, (M p).canonical c →
        r.Yields M (r.constant R c) (MvPolynomial.C ((M p).interpret c))) ∧
      (∀ a, Q.canonical a →
        r.Yields M (r.negate R a) (-Q.interpret a) ∧
        ∀ k, r.Yields M (r.power R a k) (Q.interpret a ^ k)) ∧
      (∀ a b, Q.canonical a → Q.canonical b →
        r.Yields M (r.add R a b) (Q.interpret a + Q.interpret b) ∧
        r.Yields M (r.subtract R a b) (Q.interpret a - Q.interpret b) ∧
        r.Yields M (r.multiply R a b) (Q.interpret a * Q.interpret b)) ∧
      (∀ a, r.power R a 0 = r.one R) ∧
      ∀ k, 1 ≤ k → r.power R MvPoly.zero k = .value MvPoly.zero

/-- Leading terms, degrees and the monic test are those of Mathlib (MVP-R02),
over every coefficient ring that is exact under an interpretation, in every
ring `r`, for every monomial order `m` of Mathlib that agrees with the order
of `r` (`OrderKind.Agrees`), on every canonical polynomial `a` that denotes
`A`:

* `a` has no leading term and no total degree exactly when `A = 0`;
* the leading term of `a`, its last term, has the exponent vector that
  denotes the degree of `A` under `m`, and a coefficient that denotes the
  leading coefficient of `A` under `m`;
* for `A ≠ 0`, the total degree of `a`, the largest total degree of its
  monomials, is the total degree of `A`;
* the monic test of `a` decides, and finds `a` monic exactly when `A ≠ 0`
  and the leading coefficient of `A` under `m` is 1. -/
def LeadingTermsAreThoseOfMathlib : Prop :=
  ∀ (P E : Type) (K : P → Type) [∀ p, CommRing (K p)] (R : CoefficientRing P E Empty)
    (M : Model P E K), ExactRing R M → ∀ (n : ℕ) (r : MultivariateRing P n)
    (m : MonomialOrder.{0, 0} (Fin n)), r.order.Agrees m →
      ∀ a, (MultivariateRing.model M r).canonical a →
        let A := (MultivariateRing.model M r).interpret a
        (a.leadingTerm = none ↔ A = 0) ∧ (a.totalDegree = none ↔ A = 0) ∧
        (∀ e c, a.leadingTerm = some (e, c) →
          e.toFinsupp = m.degree A ∧ (M r.coefficients).interpret c = m.leadingCoeff A) ∧
        (A ≠ 0 → a.totalDegree = some A.totalDegree) ∧
        ∃ b, a.isMonic R r.coefficients = .value b ∧ (b = true ↔ A ≠ 0 ∧ m.Monic A)

/-- Normalization gives canonical forms (MVP-R03, MVP-R04), over every
coefficient ring that is exact under an interpretation, in every ring `r`: on
every list of terms with canonical coefficients, in any order and with
repeated monomials, `normalize` returns a canonical polynomial that denotes
the sum of the terms, so the coefficients of each monomial are added and the
terms whose sum is zero are dropped; and a permutation of the list gives the
same result. -/
def NormalizationGivesCanonicalForms : Prop :=
  ∀ (P E : Type) (K : P → Type) [∀ p, CommRing (K p)] (R : CoefficientRing P E Empty)
    (M : Model P E K), ExactRing R M → ∀ (n : ℕ) (r : MultivariateRing P n)
    (ts : List (Exponents n × E)), (∀ t ∈ ts, (M r.coefficients).canonical t.2) →
      r.Yields M (r.normalize R ts) ((⟨ts⟩ : MvPoly n E).interpret M r.coefficients) ∧
      ∀ us, us.Perm ts → r.normalize R us = r.normalize R ts

/-- Expansion and the conversion back to terms keep the meaning of terms
(MVP-R06, MVP-R07). The meaning of a term is a partial function from
assignments to the complex numbers (`Term.denote`), and that of a polynomial
of a ring over `ℚ` its value at the values of the names of its variables
(`polyValue`):

* when the expansion of any term `t` in any ring `r` over `ℚ` returns the
  polynomial `a`, then `t` is defined at every assignment, under every
  interpretation, with the value of `a`;
* under a total order of terms `o`, every `maxExponent` and a lawful
  interpretation, when the conversion of a canonical polynomial `a` back to
  terms returns the term `u`, then `u` has the value of `a` at every
  assignment, and, when the names of the variables are distinct, `u` expands
  back into `a`;
* in a ring whose names pass the check of `MultivariateRing.new`, the
  conversion of a canonical polynomial returns a term unless it fails with
  `ResourceLimit` naming `max_exponent`. -/
def ExpansionAndConversionKeepMeanings : Prop :=
  (∀ (n : ℕ) (r : MultivariateRing Rationals n) (I : Interp) (t : Term) (a : MvPoly n Fraction),
    r.expand t = .value a → ∀ ρ, t.denote I ρ = some (polyValue r a ρ)) ∧
  ∀ (o : Orders) (maxExponent n : ℕ) (r : MultivariateRing Rationals n) (I : Interp), o.Total →
    I.Lawful → ∀ a : MvPoly n Fraction, a.Canonical Rationals.model r.coefficients r.order →
      (∀ u, r.toTerm o maxExponent a = .value u →
        (∀ ρ, u.denote I ρ = some (polyValue r a ρ)) ∧
        (r.variableNames.Nodup → r.expand u = .value a)) ∧
      (checkVariableNames [] r.variableNames = .value () →
        r.toTerm o maxExponent a = .resourceLimit .exponent ∨
          ∃ u, r.toTerm o maxExponent a = .value u)

/-! ## Monomial orders (FLD-R06) -/

/-- Monomial orders, positive (FLD-R06): in `ℚ[x, y, z]`, `y²z` is above
`xz²` under `grevlex`, both of degree 3, since the exponent 1 of the last
variable `z` in `y²z` is below its exponent 2 in `xz²`; and under the block
order of the split 1, `xz² > xy > y⁴`. -/
def ComparisonsUnderGrevlexAndABlockOrder : Prop :=
  (OrderKind.grevlex : OrderKind 3).compare ![0, 2, 1] ![1, 0, 2] = .gt ∧
    (OrderKind.block 1 : OrderKind 3).compare ![1, 0, 2] ![1, 1, 0] = .gt ∧
    (OrderKind.block 1 : OrderKind 3).compare ![1, 1, 0] ![0, 4, 0] = .gt

/-- Monomial orders, negative (FLD-R06): under `grevlex`, `xz²` is not above
`y²z`, which `grlex` gives; and under the block order of the split 1, `y⁴`
is not above `xy`, which both graded orders give. -/
def ComparisonsOfOtherOrdersDoNotHold : Prop :=
  (OrderKind.grevlex : OrderKind 3).compare ![1, 0, 2] ![0, 2, 1] ≠ .gt ∧
    (OrderKind.grlex : OrderKind 3).compare ![1, 0, 2] ![0, 2, 1] = .gt ∧
    (OrderKind.block 1 : OrderKind 3).compare ![0, 4, 0] ![1, 1, 0] ≠ .gt ∧
    (OrderKind.grlex : OrderKind 3).compare ![0, 4, 0] ![1, 1, 0] = .gt ∧
    (OrderKind.grevlex : OrderKind 3).compare ![0, 4, 0] ![1, 1, 0] = .gt

/-! ## Canonical forms (FLD-R01) -/

/-- Canonical forms, positive (FLD-R01): in `ℚ[x, y, z]` under `lex`, the
canonical form of `x² + xz² + y²z` holds the terms `y²z`, `xz²` and `x²` in
this order, and its last term `x²` is its leading term; and the canonical
form of the zero polynomial is the empty list. -/
def CanonicalFormOfThreeTerms : Prop :=
  let r := ratRingXYZ .lex
  let a : MvPoly 3 Fraction := ratPoly [(![0, 2, 1], 1), (![1, 0, 2], 1), (![2, 0, 0], 1)]
  let X : Fin 3 → MvPolynomial (Fin 3) ℚ := MvPolynomial.X
  r.Yields Rationals.model (.value a) (X 0 ^ 2 + X 0 * X 2 ^ 2 + X 1 ^ 2 * X 2) ∧
    a.leadingTerm = some (![2, 0, 0], Fraction.ofRat 1) ∧
    r.Yields Rationals.model (.value MvPoly.zero) 0 ∧ (MvPoly.zero : MvPoly 3 Fraction).terms = []

/-- Canonical forms, negative (FLD-R01): in `ℚ[x, y, z]` under `lex`, a list
with a term whose coefficient is zero, a list with the monomial `x²` twice,
and the list of `x²` before `xz²`, whose monomials do not increase, are not
canonical. -/
def NonCanonicalTermLists : Prop :=
  let canonical (a : MvPoly 3 Fraction) : Prop := a.Canonical Rationals.model ⟨⟩ .lex
  ¬canonical (ratPoly [(![0, 2, 1], 1), (![2, 0, 0], 0)]) ∧
    ¬canonical (ratPoly [(![2, 0, 0], 1), (![2, 0, 0], 1)]) ∧
    ¬canonical (ratPoly [(![2, 0, 0], 1), (![1, 0, 2], 1)])

/-! ## The ring (MVP-R01) -/

/-- The ring, positive (MVP-R01): the ring over `ℚ` of the variables
`x, y, z` under the block order of the split 1 is built, and so is the ring
without variables; and two rings over `ℚ` with the same parent, the same
names in the same order and the same order are the same ring, so a ring is
determined by its data. -/
def RingsAreBuiltFromTheirData : Prop :=
  MultivariateRing.new (⟨⟩ : Rationals) ["x", "y", "z"] (.block 1) =
      .value (ratRingXYZ (.block 1)) ∧
    MultivariateRing.new (⟨⟩ : Rationals) [] .lex = .value ⟨⟨⟩, [], rfl, .lex⟩ ∧
    ∀ r s : MultivariateRing Rationals 3, r.coefficients = s.coefficients →
      r.variableNames = s.variableNames → r.order = s.order → r = s

/-- The ring, negative (MVP-R01): the variables `x, x` fail with `Syntax`
without a span; the rings of `x, y` and of `y, x` are different; and so are
the rings under `grevlex` and under the block orders of the splits 0 and 2,
which order the monomials alike. -/
def RepeatedNamesAndDifferentRings : Prop :=
  MultivariateRing.new (⟨⟩ : Rationals) ["x", "x"] .lex = .fault (.term (.syntax none)) ∧
    ratRingXY .lex ≠ ⟨⟨⟩, ["y", "x"], rfl, .lex⟩ ∧
    ratRingXY .grevlex ≠ ratRingXY (.block 0) ∧ ratRingXY .grevlex ≠ ratRingXY (.block 2)

/-! ## Leading terms, degrees and monic polynomials (MVP-R02) -/

/-- Leading terms, positive (MVP-R02): in `ℚ[x, y, z]`, the leading monomial
of `xy + xz² + y⁴` is `xy` under `lex`, `y⁴` under `grlex` and `grevlex`, and
`xz²` under the block order of the split 1; its total degree is 4 under each
of them. -/
def LeadingMonomialsDependOnTheOrder : Prop :=
  let a (o : OrderKind 3) := (ratRingXYZ o).normalize rationalRing
    (ratTerms [(![1, 1, 0], 1), (![1, 0, 2], 1), (![0, 4, 0], 1)])
  (a .lex).map MvPoly.leadingMonomial = .value (some ![1, 1, 0]) ∧
    (a .grlex).map MvPoly.leadingMonomial = .value (some ![0, 4, 0]) ∧
    (a .grevlex).map MvPoly.leadingMonomial = .value (some ![0, 4, 0]) ∧
    (a (.block 1)).map MvPoly.leadingMonomial = .value (some ![1, 0, 2]) ∧
    ∀ o ∈ ([.lex, .grlex, .grevlex, .block 1] : List (OrderKind 3)),
      (a o).map MvPoly.totalDegree = .value (some 4)

/-- Monic polynomials, negative (MVP-R02): in `ℚ[x, y]`, `x - 2y²` is monic
under `lex`, whose leading term is `x`, and not under `grlex`, whose leading
term is `-2y²`; and the zero polynomial has no leading term and no total
degree. -/
def MonicDependsOnTheOrder : Prop :=
  let a (o : OrderKind 2) := (ratRingXY o).normalize rationalRing
    (ratTerms [(![1, 0], 1), (![0, 2], -2)])
  (a .lex).map MvPoly.leadingTerm = .value (some (![1, 0], Fraction.ofRat 1)) ∧
    (a .lex).bind (MvPoly.isMonic rationalRing ⟨⟩) = .value true ∧
    (a .grlex).map MvPoly.leadingTerm = .value (some (![0, 2], Fraction.ofRat (-2))) ∧
    (a .grlex).bind (MvPoly.isMonic rationalRing ⟨⟩) = .value false ∧
    (MvPoly.zero : MvPoly 2 Fraction).leadingTerm = none ∧
    (MvPoly.zero : MvPoly 2 Fraction).totalDegree = none

/-! ## Normalization (MVP-R03) -/

/-- Normalization, positive (MVP-R03): in `ℚ[x, y, z]` under `lex`, the terms
`xz²`, `x²`, `y²z` and `x²` give the polynomial of `y²z`, `xz²` and `2x²`, and
so do the same terms in another order. -/
def NormalizationSortsAndAddsTerms : Prop :=
  let r := ratRingXYZ .lex
  let a : MvPoly 3 Fraction := ratPoly [(![0, 2, 1], 1), (![1, 0, 2], 1), (![2, 0, 0], 2)]
  r.normalize rationalRing
      (ratTerms [(![1, 0, 2], 1), (![2, 0, 0], 1), (![0, 2, 1], 1), (![2, 0, 0], 1)]) =
      .value a ∧
    r.normalize rationalRing
      (ratTerms [(![2, 0, 0], 1), (![0, 2, 1], 1), (![2, 0, 0], 1), (![1, 0, 2], 1)]) =
      .value a

/-- Normalization, negative (MVP-R03): in `ℚ[x, y]`, the terms `xy` and `-xy`
give the zero polynomial, which has no term, not a term with the coefficient
0. -/
def CancellingTermsLeaveNoTerm : Prop :=
  (ratRingXY .lex).normalize rationalRing (ratTerms [(![1, 1], 1), (![1, 1], -1)]) =
    .value MvPoly.zero

/-! ## One implementation for every coefficient ring (MVP-R04) -/

/-- One implementation, positive (MVP-R04): the one normalization gives, from
the terms `3xy` and `2xy`, the polynomial `5xy` over `ℚ` and the zero
polynomial over `𝔽_5`. -/
def OneNormalizationForEveryCoefficientRing : Prop :=
  (ratRingXY .lex).normalize rationalRing (ratTerms [(![1, 1], 3), (![1, 1], 2)]) =
      .value (ratPoly [(![1, 1], 5)]) ∧
    ∃ F, PrimeField.new 5 = .built F ∧
      (⟨F, ["x", "y"], rfl, .lex⟩ : MultivariateRing PrimeField 2).normalize
        PrimeField.field.toCoefficientRing (residueTerms [(![1, 1], 3), (![1, 1], 2)]) =
        .value MvPoly.zero

/-- One implementation, negative (MVP-R04): over `𝔽_2`, the terms `xy`, `xy`
and `y` give the polynomial `y` of one term, without the term `xy` of the
coefficient `2 = 0`. -/
def TermsVanishingModuloTwoLeaveNoTerm : Prop :=
  ∃ F, PrimeField.new 2 = .built F ∧
    (⟨F, ["x", "y"], rfl, .lex⟩ : MultivariateRing PrimeField 2).normalize
      PrimeField.field.toCoefficientRing (residueTerms [(![1, 1], 1), (![1, 1], 1), (![0, 1], 1)]) =
      .value (residuePoly [(![0, 1], 1)])

/-! ## Ring operations (MVP-R05) -/

/-- Ring operations, positive (MVP-R05): in `ℚ[x, y]` under `lex`,
`(x + y) + (x - y) = 2x`; and `(x + y)(x - y) = x² - y²`, stored as the terms
`-y²` and `x²`, the last one, `x²`, the leading term. -/
def SumsAndProductsOfBinomials : Prop :=
  let r := ratRingXY .lex
  let xpy : MvPoly 2 Fraction := ratPoly [(![0, 1], 1), (![1, 0], 1)]
  let xmy : MvPoly 2 Fraction := ratPoly [(![0, 1], -1), (![1, 0], 1)]
  r.add rationalRing xpy xmy = .value (ratPoly [(![1, 0], 2)]) ∧
    (r.multiply rationalRing xpy xmy).map listedTerms =
      .value (listedTerms (ratPoly [(![0, 2], -1), (![2, 0], 1)])) ∧
    (r.multiply rationalRing xpy xmy).map (fun a => a.leadingMonomial.map List.ofFn) =
      .value (some [2, 0])

/-- Ring operations, negative (MVP-R05): in `ℚ[x, y]` under `lex`, the
product `(x + y)(x - y)` keeps no term of the monomial `xy`, whose
coefficient is zero; `x - x` is the zero polynomial, which has no term, not a
term with the coefficient 0; and so is the constant 0. -/
def ZeroCoefficientsLeaveNoTerm : Prop :=
  let r := ratRingXY .lex
  let xpy : MvPoly 2 Fraction := ratPoly [(![0, 1], 1), (![1, 0], 1)]
  let xmy : MvPoly 2 Fraction := ratPoly [(![0, 1], -1), (![1, 0], 1)]
  (r.multiply rationalRing xpy xmy).map (fun a => a.monomials.map List.ofFn) =
      .value [[0, 2], [2, 0]] ∧
    (do let x ← r.generator rationalRing 0; r.subtract rationalRing x x) = .value MvPoly.zero ∧
    r.constant rationalRing (Fraction.ofRat 0) = .value MvPoly.zero

/-! ## Integer powers (FLD-R03) -/

/-- Integer powers, positive (FLD-R03): in `ℚ[x, y]` under `lex`,
`(x + y)² = x² + 2xy + y²`; and `0⁰ = 1`. -/
def PowersOfABinomialAndOfZero : Prop :=
  let r := ratRingXY .lex
  (r.power rationalRing (ratPoly [(![0, 1], 1), (![1, 0], 1)]) 2).map listedTerms =
      .value (listedTerms (ratPoly [(![0, 2], 1), (![1, 1], 2), (![2, 0], 1)])) ∧
    (r.power rationalRing MvPoly.zero 0).map listedTerms =
      .value (listedTerms (ratPoly [(![0, 0], 1)]))

/-- Integer powers, negative (FLD-R03): over `𝔽_2`, `(x + y)² = x² + y²`,
without the term `xy` of the coefficient `2 = 0`; and in `ℚ[x, y]`, `0ᵏ` for
every `k ≥ 1` is the zero polynomial, not one. -/
def PowersModuloTwoAndPowersOfZero : Prop :=
  (∃ F, PrimeField.new 2 = .built F ∧
    ((⟨F, ["x", "y"], rfl, .lex⟩ : MultivariateRing PrimeField 2).power
      PrimeField.field.toCoefficientRing (residuePoly [(![0, 1], 1), (![1, 0], 1)]) 2).map
      listedTerms = .value (listedTerms (residuePoly [(![0, 2], 1), (![2, 0], 1)]))) ∧
  ∀ k, 1 ≤ k → (ratRingXY .lex).power rationalRing MvPoly.zero k = .value MvPoly.zero

/-! ## Expansion of terms (MVP-R06) -/

/-- Expansion, positive (MVP-R06): in `ℚ[x, y]` under `lex`, `(x + y)²`
expands to `x² + 2xy + y²`; and `(x + y)² - x² - 2xy - y²`, whose canonical
term is the sum of the monomials `-x²`, `-y²`, `(x + y)²` and `-2xy`, expands
to the zero polynomial. -/
def TermsExpandIntoPolynomials : Prop :=
  let r := ratRingXY .lex
  let x : Term := .symbol "x"
  let y : Term := .symbol "y"
  (r.expand (.power (.sum 0 [(1, x), (1, y)]) 2)).map listedTerms =
      .value (listedTerms (ratPoly [(![0, 2], 1), (![1, 1], 2), (![2, 0], 1)])) ∧
    r.expand (.sum 0 [(-1, .power x 2), (-1, .power y 2), (1, .power (.sum 0 [(1, x), (1, y)]) 2),
      (-2, .product 1 [x, y])]) = .value MvPoly.zero

/-- Expansion, negative (MVP-R06): in `ℚ[x, y]`, `x/y = x y⁻¹` fails with
`NotPolynomial`; `z` fails with `UnknownSymbol`; and `z⁻¹`, whose base is
expanded first, fails with `UnknownSymbol`, not `NotPolynomial`. -/
def ForeignSymbolsAndNegativePowersFail : Prop :=
  let r := ratRingXY .lex
  r.expand (.product 1 [.symbol "x", .power (.symbol "y") (-1)]) = .fault .notPolynomial ∧
    r.expand (.symbol "z") = .fault (.term .unknownSymbol) ∧
    r.expand (.power (.symbol "z") (-1)) = .fault (.term .unknownSymbol)

/-! ## Conversion back to terms (MVP-R07) -/

/-- Conversion back to terms, positive (MVP-R07): in `ℚ[x, y]` under `lex`,
`x² - y²` converts to the sum of the two monomials `x²` and `-y²`, which
expands back into `x² - y²`; and the zero polynomial converts to the number
0. -/
def PolynomialsConvertBackToTerms : Prop :=
  let r := ratRingXY .lex
  let a : MvPoly 2 Fraction := ratPoly [(![0, 2], -1), (![2, 0], 1)]
  let toTerm := r.toTerm Orders.sample defaultMaxExponent
  toTerm a = .value (.sum 0 [(1, .power (.symbol "x") 2), (-1, .power (.symbol "y") 2)]) ∧
    ((toTerm a).bind r.expand).map listedTerms = .value (listedTerms a) ∧
    toTerm MvPoly.zero = .value (.number 0)

/-- Conversion back to terms, negative (MVP-R07): in `ℚ[x, y]` under `lex`,
`3xy` converts to the product of the coefficient 3 and the factors `x` and
`y`, not to a sum; and the term of `x² - y²` is not the canonical term
`(x - y)(x + y)` of the same polynomial written as a product. -/
def ConversionBuildsCanonicalTerms : Prop :=
  let r := ratRingXY .lex
  let x : Term := .symbol "x"
  let y : Term := .symbol "y"
  let toTerm := r.toTerm Orders.sample defaultMaxExponent
  toTerm (ratPoly [(![1, 1], 3)]) = .value (.product 3 [x, y]) ∧
    toTerm (ratPoly [(![0, 2], -1), (![2, 0], 1)]) ≠
      .value (.product 1 [.sum 0 [(1, x), (-1, y)], .sum 0 [(1, x), (1, y)]])

end Kalyx.Statements.Multivariate

end
