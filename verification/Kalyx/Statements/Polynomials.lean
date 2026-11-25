module

public import Kalyx.Spec.Polynomials.Division
public import Kalyx.Spec.Polynomials.Evaluate
public import Kalyx.Spec.Polynomials.Maps
public import Kalyx.Spec.Polynomials.Terms
public import Kalyx.Spec.Terms.Semantics
public import Mathlib.Algebra.Polynomial.Derivative

/-!
# Statements about the univariate polynomials

The registered statements of the specification of the univariate polynomials
(`Kalyx.Spec.Polynomials`), each a proposition named here and proved, or to be
proved, by a theorem of `Kalyx.Proofs.Polynomials`. They are written from the
numbered requirements of the polynomials contract
(`docs/components/polynomials/contract.md`), whose table of requirements and
statements names, for each requirement, the statements that state it.

The first nine are the properties: the ring operations are exact under the
interpretation in Mathlib's `Polynomial`; division with remainder, the monic
GCD and the extended GCD with the cofactors of lowest degree are determined
by their defining conditions; the derivative follows the product rule;
evaluation is a homomorphism; expansion and the conversion back to terms keep
the meaning of terms; modular powers are remainders; and maps act on each
coefficient. A property holds for every coefficient ring or field of the
specification of the coefficient fields that is exact under an
interpretation (`ExactRing`, `ExactField`): its ring laws, and its field laws
for a field, hold, and its zero test is exact, as they do for the rationals,
the integers, the residue rings, the prime fields and the number fields. The
shared algorithms over a field are stated for interpretations in a field of
Mathlib. The meaning of an expansion is stated under every interpretation of
the calls, conditions and constants of terms, and that of the conversion back
to terms under every total choice of the orders of the term core
(`Orders.Total`) and every lawful interpretation (`Interp.Lawful`), the
parameters of the statements about the term core.

The others are a positive and a negative example of each requirement. The
examples fix the parameters: the limits `Limits.default` and the order
`Orders.sample`, unless an example names others. A polynomial over `ℚ` is
written as the list of its terms (`ratPoly`), and over a prime field as the
list of its residues (`residuePoly`); a prime field `𝔽_p` is the one that the
constructor builds from `p`, as in `∃ F, PrimeField.new 7 = .built F ∧ …`,
and a residue ring `ℤ/n` is the parent `⟨n⟩`, for every storage cost. A term
is written as its canonical term, the term that the term core builds from the
input, as a parse of the input text builds it.
-/

@[expose] public section

namespace Kalyx.Statements.Polynomials

open Kalyx.Spec.Fields
open Kalyx.Spec.Polynomials
open Kalyx.Spec.Terms (Term Orders Interp Assignment mkPower exponentBound)

/-! ## Notions of the statements -/

/-- The coefficient ring `R` is exact under the interpretation `M`: its ring
laws hold and its zero test is exact. -/
def ExactRing {P E : Type} {K : P → Type} [∀ p, CommRing (K p)]
    (R : CoefficientRing P E Empty) (M : Model P E K) : Prop :=
  RingLaws R M ∧ ZeroTestExact R M

/-- The coefficient field `F` is exact under `M`: its ring is exact and its
field laws hold. -/
def ExactField {P E : Type} {K : P → Type} [∀ p, CommRing (K p)]
    (F : CoefficientField P E Empty) (M : Model P E K) : Prop :=
  ExactRing F.toCoefficientRing M ∧ FieldLaws F M

/-- The result `o` of an operation of a ring under limits is a canonical
polynomial over the parent `p` under `M` that denotes `x`, or `ResourceLimit`
naming one of the fields that the checks of the polynomials read:
`max_exponent`, `max_nodes` or `max_storage_bytes`. -/
def YieldsWithinLimits {P E : Type} {K : P → Type} [∀ p, CommRing (K p)] (M : Model P E K)
    (p : P) (o : PolyResult (Poly E)) (x : Polynomial (K p)) : Prop :=
  Poly.Yields M p o x ∨ o = .resourceLimit .exponent ∨ o = .resourceLimit .nodes ∨
    o = .resourceLimit .storageBytes

/-- The result `o` is a canonical element of the parent `p` under `M` that
denotes `x`. -/
def YieldsElement {P E : Type} {K : P → Type} (M : Model P E K) (p : P) (o : PolyResult E)
    (x : K p) : Prop :=
  ∃ e, o = .value e ∧ (M p).canonical e ∧ (M p).interpret e = x

/-- `G` is a monic GCD of `A` and `B` (FLD-R09): it is monic when `A` and `B`
are not both zero and zero when they are, it divides `A` and `B`, and every
common divisor of `A` and `B` divides it. -/
def MonicGcdOf {K : Type} [Field K] (A B G : Polynomial K) : Prop :=
  (A = 0 ∧ B = 0 → G = 0) ∧ (A ≠ 0 ∨ B ≠ 0 → G.Monic) ∧ G ∣ A ∧ G ∣ B ∧
    ∀ D, D ∣ A → D ∣ B → D ∣ G

/-- The value of the polynomial `a` of the ring `r` over `ℚ` at the
assignment `ρ`: the polynomial of Mathlib that `a` denotes, with its rational
coefficients taken into the complex numbers, at the value of the variable in
`ρ`. -/
noncomputable def polyValue (r : PolynomialRing Rationals) (a : Poly Fraction)
    (ρ : Assignment) : ℂ :=
  (a.interpret Rationals.model r.coefficients).eval₂ (Rat.castHom ℂ) (ρ r.variableName)

/-- The polynomial over `ℚ` with the terms `(d, c)` of `l`, each coefficient
the reduced fraction of `c`. -/
def ratPoly (l : List (ℕ × ℚ)) : Poly Fraction := ⟨l.map fun t => (t.1, Fraction.ofRat t.2)⟩

/-- The polynomial over a prime field with the terms `(d, c)` of `l`, each
coefficient the residue `c`. -/
def residuePoly (l : List (ℕ × ℕ)) : Poly PrimeResidue := ⟨l.map fun t => (t.1, ⟨t.2⟩)⟩

/-- The ring `ℚ[x]` of the variable `name`. -/
def ratRing (name : String) : PolynomialRing Rationals := ⟨⟨⟩, name⟩

/-! ## Properties -/

/-- The ring operations are exact (FLD-R01, FLD-R03, FLD-R04, POL-R10,
POL-R11), over every coefficient ring `R` whose zero test always decides and
that is exact under the interpretation `M` (`ExactRing`):

* canonical forms are unique: two canonical polynomials of a ring that denote
  the same polynomial of Mathlib are equal;
* the operations without the checks, which the shared algorithms use, return
  on canonical operands a canonical polynomial that denotes the negation, the
  sum, the difference and the product in `Polynomial (K p)`, and the
  monomial `c xᵈ` of a canonical coefficient `c`;
* under every limits `L`, `zero`, `one`, `generator`, `constant`, `negate`,
  `add`, `subtract`, `multiply` and `power` of a ring return a canonical
  polynomial that denotes `0`, `1`, `X`, the constant, the negation, the sum,
  the difference, the product and the power `Aᵏ`, or fail with
  `ResourceLimit` naming a field that the checks read
  (`YieldsWithinLimits`); no fault and no other failure is possible;
* `a⁰` is the polynomial one for every `a`, `0⁰` included, and `0ᵏ` for
  `k ≥ 1` within the bound on exponents is the zero polynomial, checked as
  every result. -/
def RingOperationsAreExact : Prop :=
  ∀ (P E : Type) (K : P → Type) [∀ p, CommRing (K p)] (R : CoefficientRing P E Empty)
    (M : Model P E K), ExactRing R M →
    (∀ r : PolynomialRing P, (PolynomialRing.model M r).Unique) ∧
    (∀ p a, a.Canonical M p → Poly.Yields M p (Poly.negate R p a) (-a.interpret M p)) ∧
    (∀ p a b, a.Canonical M p → b.Canonical M p →
      Poly.Yields M p (Poly.sum R p a b) (a.interpret M p + b.interpret M p) ∧
      Poly.Yields M p (Poly.difference R p a b) (a.interpret M p - b.interpret M p) ∧
      Poly.Yields M p (Poly.product R p .value a b) (a.interpret M p * b.interpret M p)) ∧
    (∀ p d c, (M p).canonical c →
      Poly.Yields M p (Poly.monomial R p d c) (Polynomial.monomial d ((M p).interpret c))) ∧
    ∀ (L : Limits) (r : PolynomialRing P),
      let p := r.coefficients
      YieldsWithinLimits M p (r.zero R L) 0 ∧
      YieldsWithinLimits M p (r.one R L) 1 ∧
      YieldsWithinLimits M p (r.generator R L) Polynomial.X ∧
      (∀ c, (M p).canonical c →
        YieldsWithinLimits M p (r.constant R L c) (Polynomial.C ((M p).interpret c))) ∧
      (∀ a, a.Canonical M p →
        YieldsWithinLimits M p (r.negate R L a) (-a.interpret M p) ∧
        (∀ k, YieldsWithinLimits M p (r.power R L a k) (a.interpret M p ^ k)) ∧
        r.power R L a 0 = r.one R L) ∧
      (∀ a b, a.Canonical M p → b.Canonical M p →
        YieldsWithinLimits M p (r.add R L a b) (a.interpret M p + b.interpret M p) ∧
        YieldsWithinLimits M p (r.subtract R L a b) (a.interpret M p - b.interpret M p) ∧
        YieldsWithinLimits M p (r.multiply R L a b) (a.interpret M p * b.interpret M p)) ∧
      ∀ k, 1 ≤ k → k ≤ exponentBound L.maxExponent → r.power R L Poly.zero k = r.zero R L

/-- Division with remainder is determined by its conditions (FLD-R08), over
every coefficient field `F` that is exact under an interpretation `M` in
fields: a division by the zero polynomial, and the remainder alone, fail with
`DivisionByZero`, whatever the dividend; otherwise, on canonical operands,
`Poly.divRem` returns canonical `(q, r)` whose interpretations satisfy
`a = q b + r` and `deg r < deg b`, every pair of polynomials of Mathlib that
satisfies these two conditions is that pair, and the remainder alone
(`Poly.rem`) is `r`. -/
def DivisionWithRemainderIsUnique : Prop :=
  ∀ (P E : Type) (K : P → Type) [∀ p, Field (K p)] (F : CoefficientField P E Empty)
    (M : Model P E K), ExactField F M →
    (∀ p a, Poly.divRem F p a Poly.zero = .fault (.field .divisionByZero) ∧
      Poly.rem F p a Poly.zero = .fault (.field .divisionByZero)) ∧
    ∀ p a b, a.Canonical M p → b.Canonical M p → b ≠ Poly.zero →
      let A := a.interpret M p
      let B := b.interpret M p
      ∃ q r, Poly.divRem F p a b = .value (q, r) ∧ q.Canonical M p ∧ r.Canonical M p ∧
        A = q.interpret M p * B + r.interpret M p ∧ (r.interpret M p).degree < B.degree ∧
        (∀ Q₁ R₁ : Polynomial (K p), A = Q₁ * B + R₁ → R₁.degree < B.degree →
          Q₁ = q.interpret M p ∧ R₁ = r.interpret M p) ∧
        Poly.rem F p a b = .value r

/-- The monic GCD is determined by its conditions (FLD-R09), over every
coefficient field that is exact under an interpretation in fields: the monic
form of a canonical polynomial is canonical and denotes it times the inverse
of its leading coefficient, zero for zero; the GCD of `a` and the zero
polynomial is the monic form of `a`; and the GCD of canonical `a` and `b` is
canonical and a monic GCD of their interpretations (`MonicGcdOf`): monic
unless both are zero, zero when both are, a common divisor that every common
divisor divides. Every polynomial of Mathlib with these conditions is the
GCD, and `a` and `b` are coprime exactly when their GCD is one. -/
def MonicGcdIsUnique : Prop :=
  ∀ (P E : Type) (K : P → Type) [∀ p, Field (K p)] (F : CoefficientField P E Empty)
    (M : Model P E K), ExactField F M →
    (∀ p a, a.Canonical M p →
      Poly.Yields M p (Poly.monicForm F p a)
        (a.interpret M p * Polynomial.C (a.interpret M p).leadingCoeff⁻¹) ∧
      Poly.monicGcd F p a Poly.zero = Poly.monicForm F p a) ∧
    ∀ p a b, a.Canonical M p → b.Canonical M p →
      let A := a.interpret M p
      let B := b.interpret M p
      ∃ g, Poly.monicGcd F p a b = .value g ∧ g.Canonical M p ∧
        MonicGcdOf A B (g.interpret M p) ∧ (∀ G, MonicGcdOf A B G → G = g.interpret M p) ∧
        (IsRelPrime A B ↔ g.interpret M p = 1)

/-- The extended GCD has the cofactors of lowest degree (POL-R12), over every
coefficient field that is exact under an interpretation in fields: on
canonical `a` and `b`, `Poly.extendedGcd` returns canonical cofactors `s` and
`t` and the GCD `g` of `Poly.monicGcd`, with `s a + t b = g` in Mathlib and
the conditions of the cofactors of lowest degree (`Poly.lowestCofactors`);
every canonical pair of cofactors with `s a + t b = g` and these conditions
is that pair. -/
def ExtendedGcdHasLowestCofactors : Prop :=
  ∀ (P E : Type) (K : P → Type) [∀ p, Field (K p)] (F : CoefficientField P E Empty)
    (M : Model P E K), ExactField F M →
    ∀ p a b, a.Canonical M p → b.Canonical M p →
      let A := a.interpret M p
      let B := b.interpret M p
      ∃ e : Bezout E, Poly.extendedGcd F p a b = .value e ∧
        e.left.Canonical M p ∧ e.right.Canonical M p ∧ Poly.monicGcd F p a b = .value e.gcd ∧
        e.left.interpret M p * A + e.right.interpret M p * B = e.gcd.interpret M p ∧
        Poly.lowestCofactors a b e.left e.right e.gcd = true ∧
        ∀ s t, s.Canonical M p → t.Canonical M p →
          s.interpret M p * A + t.interpret M p * B = e.gcd.interpret M p →
          Poly.lowestCofactors a b s t e.gcd = true → s = e.left ∧ t = e.right

/-- The derivative follows the product rule (POL-R07, POL-R10, POL-R11), over
every coefficient ring that is exact under an interpretation, in every
characteristic: on a canonical polynomial, the derivative without the checks
returns a canonical polynomial that denotes Mathlib's `derivative`, and the
derivative of a ring under every limits returns it or fails with
`ResourceLimit` (`YieldsWithinLimits`). So, on canonical operands, the
derivative of a sum is the sum of the derivatives, and the derivative of a
product `a b` is `a′ b + a b′`, each formed by the operations without the
checks; with a constant for `a`, the derivative is linear. -/
def DerivativeFollowsTheProductRule : Prop :=
  ∀ (P E : Type) (K : P → Type) [∀ p, CommRing (K p)] (R : CoefficientRing P E Empty)
    (M : Model P E K), ExactRing R M →
    (∀ p a, a.Canonical M p →
      Poly.Yields M p (Poly.derivative R p a) (Polynomial.derivative (a.interpret M p))) ∧
    (∀ (L : Limits) (r : PolynomialRing P) a, a.Canonical M r.coefficients →
      YieldsWithinLimits M r.coefficients (r.derivative R L a)
        (Polynomial.derivative (a.interpret M r.coefficients))) ∧
    ∀ p a b, a.Canonical M p → b.Canonical M p →
      (Poly.sum R p a b).bind (Poly.derivative R p) =
        (do Poly.sum R p (← Poly.derivative R p a) (← Poly.derivative R p b)
          : PolyResult (Poly E)) ∧
      (Poly.product R p .value a b).bind (Poly.derivative R p) =
        (do
          let u ← Poly.product R p .value (← Poly.derivative R p a) b
          let v ← Poly.product R p .value a (← Poly.derivative R p b)
          Poly.sum R p u v : PolyResult (Poly E))

/-- Evaluation is a homomorphism (POL-R14). Over every coefficient ring whose
ring laws hold under an interpretation, whatever its zero test, the value of a
canonical polynomial at a canonical element is a canonical element that
denotes Mathlib's `eval` of the interpretations. Over a coefficient ring that
is exact, on canonical operands, the value of a sum and of a product is the
sum and the product of the values, formed by the coefficient ring, and the
value of the polynomial one is one. -/
def EvaluationIsAHomomorphism : Prop :=
  (∀ (P E U : Type) (K : P → Type) [∀ p, CommRing (K p)] (R : CoefficientRing P E U)
    (M : Model P E K), RingLaws R M →
    ∀ p a c, a.Canonical M p → (M p).canonical c →
      YieldsElement M p (Poly.eval R p a c) ((a.interpret M p).eval ((M p).interpret c))) ∧
  ∀ (P E : Type) (K : P → Type) [∀ p, CommRing (K p)] (R : CoefficientRing P E Empty)
    (M : Model P E K), ExactRing R M →
    ∀ p a b c, a.Canonical M p → b.Canonical M p → (M p).canonical c →
      (Poly.sum R p a b).bind (fun s => Poly.eval R p s c) =
        (do PolyResult.ofOutcome (R.add p (← Poly.eval R p a c) (← Poly.eval R p b c))
          : PolyResult E) ∧
      (Poly.product R p .value a b).bind (fun s => Poly.eval R p s c) =
        (do PolyResult.ofOutcome (R.multiply p (← Poly.eval R p a c) (← Poly.eval R p b c))
          : PolyResult E) ∧
      (Poly.monomial R p 0 (R.one p)).bind (fun s => Poly.eval R p s c) = .value (R.one p)

/-- Expansion and the conversion back to terms keep the meaning of terms
(POL-R04, POL-R06). The meaning of a term is a partial function from
assignments to the complex numbers (`Term.denote`), and that of a polynomial
of `ℚ[x]` its value at the value of the variable (`polyValue`):

* when the expansion of any term `t` under any limits returns the polynomial
  `a`, then `t` is defined at every assignment, under every interpretation,
  with the value of `a`;
* under a total order and a lawful interpretation, when the conversion of a
  canonical polynomial `a` back to terms returns the term `u`, then `u` has
  the value of `a` at every assignment, and under limits that admit `a` and
  the depth of `u`, `u` expands back into `a`. -/
def ExpansionKeepsMeanings : Prop :=
  (∀ (L : Limits) (r : PolynomialRing Rationals) (I : Interp) (t : Term) (a : Poly Fraction),
    r.expand L t = .value a → ∀ ρ, t.denote I ρ = some (polyValue r a ρ)) ∧
  ∀ (o : Orders) (L : Limits) (r : PolynomialRing Rationals) (I : Interp), o.Total →
    I.Lawful → ∀ (a : Poly Fraction) (u : Term), a.Canonical Rationals.model r.coefficients →
      r.toTerm o L a = .value u →
      (∀ ρ, u.denote I ρ = some (polyValue r a ρ)) ∧
      (u.depth ≤ L.maxDepth → r.check rationalRing L a = .value a → r.expand L u = .value a)

/-- Modular powers are remainders (POL-R13), over every coefficient field that
is exact under an interpretation in fields: a modular power by the zero
polynomial fails with `DivisionByZero`, whatever the base and the exponent;
otherwise, on canonical operands, it is a canonical polynomial `s` of degree
below that of `m` with `aᵏ = Q m + s` for some polynomial `Q`, the remainder
of `aᵏ` by `m`, for every `k`, `k = 0` included. -/
def ModularPowersAreRemainders : Prop :=
  ∀ (P E : Type) (K : P → Type) [∀ p, Field (K p)] (F : CoefficientField P E Empty)
    (M : Model P E K), ExactField F M →
    (∀ p a k, Poly.powerMod F p a k Poly.zero = .fault (.field .divisionByZero)) ∧
    ∀ p a k m, a.Canonical M p → m.Canonical M p → m ≠ Poly.zero →
      ∃ s, Poly.powerMod F p a k m = .value s ∧ s.Canonical M p ∧
        (s.interpret M p).degree < (m.interpret M p).degree ∧
        ∃ Q, a.interpret M p ^ k = Q * m.interpret M p + s.interpret M p

/-- Maps act on each coefficient (FLD-R11). The meaning of the map of a
polynomial by a partial homomorphism `φ` (`mapPoly`) is defined exactly when
every coefficient lies in the domain of `φ`, and is then the polynomial of the
images of the coefficients; where defined, it preserves sums and products;
and for a total homomorphism it is always defined and is `Polynomial.map`.
The map of a canonical polynomial by a map of coefficients that realizes `φ`,
such as each edge of the homomorphism graph, into a coefficient ring that is
exact, denotes it (`Poly.MapYields`): the result state `notInDomain` exactly
where `mapPoly` is undefined, and otherwise a canonical polynomial without
the coefficients whose image is zero; never a fault. -/
def MapsActOnEachCoefficient : Prop :=
  (∀ (K L : Type) [CommRing K] [CommRing L] (φ : PartialHom K L) (A : Polynomial K),
    (mapPoly φ A = none ↔ ∃ n, A.coeff n ∉ φ.domain) ∧
    ∀ B, mapPoly φ A = some B ↔
      ∃ h : ∀ n, A.coeff n ∈ φ.domain, ∀ n, B.coeff n = φ.map ⟨A.coeff n, h n⟩) ∧
  (∀ (K L : Type) [CommRing K] [CommRing L] (φ : PartialHom K L) (A B : Polynomial K)
    (A' B' : Polynomial L), mapPoly φ A = some A' → mapPoly φ B = some B' →
    mapPoly φ (A + B) = some (A' + B') ∧ mapPoly φ (A * B) = some (A' * B')) ∧
  (∀ (K L : Type) [CommRing K] [CommRing L] (g : K →+* L) (A : Polynomial K),
    mapPoly (PartialHom.ofRingHom g) A = some (A.map g)) ∧
  ∀ (P₁ E₁ P₂ E₂ : Type) (K : P₁ → Type) (L : P₂ → Type) [∀ s, CommRing (K s)]
    [∀ t, CommRing (L t)] (f : CoefficientMap P₁ E₁ P₂ E₂) (R : CoefficientRing P₂ E₂ Empty)
    (M₁ : Model P₁ E₁ K) (M₂ : Model P₂ E₂ L) (s : P₁) (t : P₂) (φ : PartialHom (K s) (L t)),
    ExactRing R M₂ → f.Realizes M₁ M₂ s t φ → ∀ a, a.Canonical M₁ s →
      Poly.MapYields M₂ t (Poly.map f R s t a) (MapResult.ofOption (mapPoly φ (a.interpret M₁ s)))

/-! ## Canonical forms (FLD-R01) -/

/-- Canonical forms, positive (FLD-R01): over `ℚ`, `(x + 1) + (x - 1)` is the
polynomial `2x` of one term, and `(x + 1)² - x² - 2x - 1` is the zero
polynomial, which has no term. -/
def SumsKeepOneTermOrNone : Prop :=
  let L := Limits.default
  let r := ratRing "x"
  let R := rationalRing
  r.add R L (ratPoly [(0, 1), (1, 1)]) (ratPoly [(0, -1), (1, 1)]) = .value (ratPoly [(1, 2)]) ∧
    (do
      let s ← r.power R L (ratPoly [(0, 1), (1, 1)]) 2
      let s ← r.subtract R L s (ratPoly [(2, 1)])
      let s ← r.subtract R L s (ratPoly [(1, 2)])
      r.subtract R L s (ratPoly [(0, 1)]) : PolyResult (Poly Fraction)) = .value Poly.zero

/-- Canonical forms, negative (FLD-R01): the term lists `[(1, 1), (0, 1)]`,
whose degrees do not increase, and `[(0, 0)]`, whose coefficient is zero, are
not canonical polynomials over `ℚ`. -/
def NonCanonicalTermLists : Prop :=
  ¬(ratPoly [(1, 1), (0, 1)]).Canonical Rationals.model ⟨⟩ ∧
    ¬(ratPoly [(0, 0)]).Canonical Rationals.model ⟨⟩

/-! ## Integer powers (FLD-R03) -/

/-- Integer powers, positive (FLD-R03): over `ℚ`, `0⁰ = 1` and
`(x + 1)² = x² + 2x + 1`. -/
def PowersOfZeroAndOfABinomial : Prop :=
  let L := Limits.default
  let r := ratRing "x"
  r.power rationalRing L Poly.zero 0 = .value (ratPoly [(0, 1)]) ∧
    r.power rationalRing L (ratPoly [(0, 1), (1, 1)]) 2 = .value (ratPoly [(0, 1), (1, 2), (2, 1)])

/-- Integer powers, negative (FLD-R03): under `maxExponent = 1` the square of
the constant 2 fails with `ResourceLimit` naming `max_exponent`, since the
exponent 2 is checked before the degree 0 of the result; under
`maxExponent = 150`, `(x¹⁰⁰ + 1)²` fails the same way, at its degree 200. -/
def PowersCheckTheExponentFirst : Prop :=
  let r := ratRing "x"
  r.power rationalRing { Limits.default with maxExponent := 1 } (ratPoly [(0, 2)]) 2 =
      .resourceLimit .exponent ∧
    r.power rationalRing { Limits.default with maxExponent := 150 } (ratPoly [(0, 1), (100, 1)])
      2 = .resourceLimit .exponent

/-! ## Zero tests (FLD-R04) -/

/-- Zero tests, positive (FLD-R04): over `𝔽_7`, `(x + 1)⁷ = x⁷ + 1`; the
binomial coefficients between, which the zero test finds zero, leave no
term. -/
def BinomialCoefficientsVanishModuloSeven : Prop :=
  ∃ F, PrimeField.new 7 = .built F ∧
    (⟨F, "x"⟩ : PolynomialRing PrimeField).power PrimeField.field.toCoefficientRing
      Limits.default (residuePoly [(0, 1), (1, 1)]) 7 = .value (residuePoly [(0, 1), (7, 1)])

/-- Zero tests, negative (FLD-R04): over `ℤ/6`, for every storage cost,
`(2x)(3x)` is the zero polynomial; the product `6 ≡ 0` of the coefficients
leaves no term. -/
def ZeroDivisorsLeaveNoTerm : Prop :=
  ∀ μ : ResidueRing → ℕ → Storage,
    (⟨⟨6⟩, "x"⟩ : PolynomialRing ResidueRing).multiply (ResidueRing.ring μ).toCoefficientRing
      Limits.default ⟨[(1, 2)]⟩ ⟨[(1, 3)]⟩ = .value Poly.zero

/-! ## Accounting under the request context (FLD-R12) -/

/-- Results under explicit limits, positive (FLD-R12): `(x + 1)²` is
`x² + 2x + 1` under `maxExponent = 2` and under the wider
`maxExponent = 100`. -/
def PowersAgreeUnderWiderLimits : Prop :=
  let r := ratRing "x"
  r.power rationalRing { Limits.default with maxExponent := 2 } (ratPoly [(0, 1), (1, 1)]) 2 =
      .value (ratPoly [(0, 1), (1, 2), (2, 1)]) ∧
    r.power rationalRing { Limits.default with maxExponent := 100 } (ratPoly [(0, 1), (1, 1)])
      2 = .value (ratPoly [(0, 1), (1, 2), (2, 1)])

/-- Results under explicit limits, negative (FLD-R12): under
`maxExponent = 1` the same power fails with `ResourceLimit` naming
`max_exponent`, the field that it exceeds, and with no other failure. -/
def ExceededLimitsNameTheirField : Prop :=
  (ratRing "x").power rationalRing { Limits.default with maxExponent := 1 }
    (ratPoly [(0, 1), (1, 1)]) 2 = .resourceLimit .exponent

/-! ## The ring and its variable (POL-R01) -/

/-- The variable of a ring, positive (POL-R01): the ring of `ℚ` with the
variable `t_1` is built. -/
def RingOfAVariableName : Prop :=
  PolynomialRing.new (⟨⟩ : Rationals) "t_1" = .value (ratRing "t_1")

/-- The variable of a ring, negative (POL-R01): the variable `pi` fails with
`Unsupported` and the span of the name; the empty name with `Syntax` and the
empty span at 0; and `1x` with `Syntax` and the span of the digit. -/
def ReservedAndMalformedVariables : Prop :=
  PolynomialRing.new (⟨⟩ : Rationals) "pi" = .fault (.term (.unsupported (some ⟨0, 2⟩))) ∧
    PolynomialRing.new (⟨⟩ : Rationals) "" = .fault (.term (.syntax (some ⟨0, 0⟩))) ∧
    PolynomialRing.new (⟨⟩ : Rationals) "1x" = .fault (.term (.syntax (some ⟨0, 1⟩)))

/-! ## The variable of a request (POL-R02) -/

/-- The variable of a request, positive (POL-R02): with the variable `t`, the
derivative of `(1/3) t³` is `t²`. -/
def DerivativeByANamedVariable : Prop :=
  let t : Term := .symbol "t"
  diffOperation Orders.sample Limits.default "t" (.product (1 / 3) [.power t 3]) =
    .value (.power t 2)

/-- The variable of a request, negative (POL-R02): with the variable `!`, the
input `y` fails with `Syntax` without a span, not with `UnknownSymbol`, since
the variable is checked before the input; and names are case-sensitive, so
with the variable `X` the input `x` fails with `UnknownSymbol`. -/
def TheVariableIsCheckedBeforeTheInput : Prop :=
  let o := Orders.sample
  let L := Limits.default
  diffOperation o L "!" (.symbol "y") = .fault (.term (.syntax none)) ∧
    expandOperation o L "!" (.symbol "y") = .fault (.term (.syntax none)) ∧
    expandOperation o L "X" (.symbol "x") = .fault (.term .unknownSymbol)

/-! ## Limits of the degree and of the number of terms (POL-R03) -/

/-- Storage, positive (POL-R03): in the variable `x`, the storage cost of
`x²⁵⁶ - 1` is 7 nodes and 36 bytes. -/
def StorageOfASparsePolynomial : Prop :=
  (ratRing "x").storage rationalRing (ratPoly [(0, -1), (256, 1)]) = ⟨7, 36⟩

/-- Storage, negative (POL-R03): under `maxNodes = 40`,
`1 + x + … + x⁹`, of 53 nodes, fails with `ResourceLimit` naming `max_nodes`;
and under `maxNodes = 28`, `(1 + x + x²)(1 - x² + x⁴)` fails the same way at
a partial sum of its rows, although the product
`1 + x - x³ + x⁵ + x⁶` itself passes the check. -/
def NodesBoundTermsAndPartialSums : Prop :=
  let r := ratRing "x"
  r.check rationalRing { Limits.default with maxNodes := 40 }
      (ratPoly ((List.range 10).map fun d => (d, 1))) = .resourceLimit .nodes ∧
    r.multiply rationalRing { Limits.default with maxNodes := 28 }
      (ratPoly [(0, 1), (1, 1), (2, 1)]) (ratPoly [(0, 1), (2, -1), (4, 1)]) =
      .resourceLimit .nodes ∧
    r.check rationalRing { Limits.default with maxNodes := 28 }
      (ratPoly [(0, 1), (1, 1), (3, -1), (5, 1), (6, 1)]) =
      .value (ratPoly [(0, 1), (1, 1), (3, -1), (5, 1), (6, 1)])

/-! ## Expansion of terms (POL-R04) -/

/-- Expansion, positive (POL-R04): `(x + 1)² - x² - 2x - 1`, whose canonical
term is the sum of `-1` and the monomials `-2x`, `-x²` and `(x + 1)²`,
expands to the zero polynomial; and `(x/2 + 1/3)³`, whose canonical term is
`(1/8) (x + 2/3)³`, to `1/8 x³ + 1/4 x² + 1/6 x + 1/27`. -/
def TermsExpandIntoPolynomials : Prop :=
  let L := Limits.default
  let r := ratRing "x"
  let x : Term := .symbol "x"
  r.expand L (.sum (-1) [(-2, x), (-1, .power x 2), (1, .power (.sum 1 [(1, x)]) 2)]) =
      .value Poly.zero ∧
    r.expand L (.product (1 / 8) [.power (.sum (2 / 3) [(1, x)]) 3]) =
      .value (ratPoly [(0, 1 / 27), (1, 1 / 6), (2, 1 / 4), (3, 1 / 8)])

/-- Expansion, negative (POL-R04): `y⁻¹` fails with `UnknownSymbol`, at the
symbol `y` in its base; and `x x⁻¹`, which the term core keeps as a witness,
fails with `NotPolynomial`. -/
def ForeignSymbolsAndNegativePowersFail : Prop :=
  let L := Limits.default
  let r := ratRing "x"
  let x : Term := .symbol "x"
  r.expand L (.power (.symbol "y") (-1)) = .fault (.term .unknownSymbol) ∧
    r.expand L (.product 1 [x, .power x (-1)]) = .fault .notPolynomial

/-! ## Order of failures (POL-R05) -/

/-- The order of failures, positive (POL-R05): `(x + y)⁻¹` fails with
`UnknownSymbol` at `y` in its base, before its negative exponent; and
`y / x = x⁻¹ y`, whose factors are sorted with `x⁻¹` first, fails with
`NotPolynomial`. -/
def FailuresFollowTheWalk : Prop :=
  let L := Limits.default
  let r := ratRing "x"
  let x : Term := .symbol "x"
  let y : Term := .symbol "y"
  r.expand L (.power (.sum 0 [(1, x), (1, y)]) (-1)) = .fault (.term .unknownSymbol) ∧
    r.expand L (.product 1 [.power x (-1), y]) = .fault .notPolynomial

/-- The order of failures, negative (POL-R05): only the first failure is
reported. `x / y = x y⁻¹` fails with `UnknownSymbol`, not `NotPolynomial`;
and under `maxExponent = 50`, `x¹⁰⁰ z` fails with `ResourceLimit` naming
`max_exponent` at its first factor, while `z + x¹⁰⁰` fails with
`UnknownSymbol` at its first core. -/
def OnlyTheFirstFailureIsReported : Prop :=
  let L := Limits.default
  let r := ratRing "x"
  let x : Term := .symbol "x"
  let y : Term := .symbol "y"
  let z : Term := .symbol "z"
  r.expand L (.product 1 [x, .power y (-1)]) = .fault (.term .unknownSymbol) ∧
    r.expand { L with maxExponent := 50 } (.product 1 [.power x 100, z]) =
      .resourceLimit .exponent ∧
    r.expand { L with maxExponent := 50 } (.sum 0 [(1, z), (1, .power x 100)]) =
      .fault (.term .unknownSymbol)

/-! ## Conversion back to terms (POL-R06) -/

/-- Conversion back to terms, positive (POL-R06): `x² - 1` converts to the sum
`-1 + x²`, and the zero polynomial to the number 0. -/
def PolynomialsConvertBackToTerms : Prop :=
  let o := Orders.sample
  let L := Limits.default
  let r := ratRing "x"
  r.toTerm o L (ratPoly [(0, -1), (2, 1)]) = .value (.sum (-1) [(1, .power (.symbol "x") 2)]) ∧
    r.toTerm o L Poly.zero = .value (.number 0)

/-- Conversion back to terms, negative (POL-R06): `3x` converts to the product
`3 x`, not a sum; and the term of `x² - 1` is not the canonical term
`(x - 1)(x + 1)` of the same polynomial written as a product. -/
def ConversionBuildsCanonicalTerms : Prop :=
  let o := Orders.sample
  let L := Limits.default
  let r := ratRing "x"
  let x : Term := .symbol "x"
  r.toTerm o L (ratPoly [(1, 3)]) = .value (.product 3 [x]) ∧
    r.toTerm o L (ratPoly [(0, -1), (2, 1)]) ≠
      .value (.product 1 [.sum (-1) [(1, x)], .sum 1 [(1, x)]])

/-! ## Differentiation (POL-R07) -/

/-- Differentiation, positive (POL-R07): over `ℚ`, the derivative of
`(x + 1)⁵` is `5x⁴ + 20x³ + 30x² + 20x + 5`; and the derivative of the term
`(t³ - 2t)/3`, whose canonical term is `-2/3 t + 1/3 t³`, by `t` is
`t² - 2/3`. -/
def DerivativesOfPolynomialsAndTerms : Prop :=
  let L := Limits.default
  let r := ratRing "x"
  let t : Term := .symbol "t"
  (r.power rationalRing L (ratPoly [(0, 1), (1, 1)]) 5).bind (r.derivative rationalRing L) =
      .value (ratPoly [(0, 5), (1, 20), (2, 30), (3, 20), (4, 5)]) ∧
    diffOperation Orders.sample L "t" (.sum 0 [(-2 / 3, t), (1 / 3, .power t 3)]) =
      .value (.sum (-2 / 3) [(1, .power t 2)])

/-- Differentiation, negative (POL-R07): over `𝔽_7`, the derivative of `x⁷` is
the zero polynomial, since `7 · 1 = 0`; and the derivative of `x + y` fails
with `UnknownSymbol`, in the expansion that comes first. -/
def DerivativesThatVanishOrFail : Prop :=
  (∃ F, PrimeField.new 7 = .built F ∧
    (⟨F, "x"⟩ : PolynomialRing PrimeField).derivative PrimeField.field.toCoefficientRing
      Limits.default (residuePoly [(7, 1)]) = .value Poly.zero) ∧
  diffOperation Orders.sample Limits.default "x" (.sum 0 [(1, .symbol "x"), (1, .symbol "y")]) =
    .fault (.term .unknownSymbol)

/-! ## The answer vectors (POL-R08) -/

/-- The answer vectors, positive (POL-R08): the vector `binomial`, `expand` of
`(x+1)^5`, gives the canonical term of `x^5 + 5*x^4 + 10*x^3 + 10*x^2 + 5*x
+ 1`. -/
def BinomialVectorExpands : Prop :=
  let x : Term := .symbol "x"
  expandOperation Orders.sample Limits.default "x" (.power (.sum 1 [(1, x)]) 5) =
    .value (.sum 1 [(5, x), (10, .power x 2), (10, .power x 3), (5, .power x 4), (1, .power x 5)])

/-- The answer vectors, negative (POL-R08): the vector `degree_limit_1`,
`expand` of `x^257` under `max_exponent=256`, fails with `ResourceLimit`
naming `max_exponent`: the term core reports it when it builds `x²⁵⁷` under
that limit, and the expansion of `x²⁵⁷`, built under wider limits, reports it
under that limit. -/
def DegreeLimitVectorFails : Prop :=
  let x : Term := .symbol "x"
  mkPower Orders.sample 256 x 257 = .resourceLimit .exponent ∧
    expandOperation Orders.sample { Limits.default with maxExponent := 256 } "x" (.power x 257) =
      .resourceLimit .exponent

/-! ## Deep terms on a small stack (POL-R09) -/

/-- Depth, positive (POL-R09): `(x + 1)²` has the depth 3 and expands under
`maxDepth = 3`. -/
def TermsWithinTheDepthExpand : Prop :=
  let t : Term := .power (.sum 1 [(1, .symbol "x")]) 2
  t.depth = 3 ∧
    (ratRing "x").expand { Limits.default with maxDepth := 3 } t =
      .value (ratPoly [(0, 1), (1, 2), (2, 1)])

/-- Depth, negative (POL-R09): `(x + y)²` has the depth 3; under
`maxDepth = 2` it fails at the entry with `ResourceLimit` naming `max_depth`,
before the symbol `y`, at which it fails with `UnknownSymbol` under
`maxDepth = 3`. -/
def DeeperTermsFailAtTheEntry : Prop :=
  let t : Term := .power (.sum 0 [(1, .symbol "x"), (1, .symbol "y")]) 2
  t.depth = 3 ∧
    (ratRing "x").expand { Limits.default with maxDepth := 2 } t = .resourceLimit .depth ∧
    (ratRing "x").expand { Limits.default with maxDepth := 3 } t = .fault (.term .unknownSymbol)

/-! ## One shared implementation (POL-R10) -/

/-- One implementation, positive (POL-R10): the one product of the
polynomials gives `(x + 1)(x - 1) = x² - 1` over `ℚ` and `x² + 4` over
`𝔽_5`. -/
def OneProductForEveryCoefficientRing : Prop :=
  (ratRing "x").multiply rationalRing Limits.default (ratPoly [(0, 1), (1, 1)])
      (ratPoly [(0, -1), (1, 1)]) = .value (ratPoly [(0, -1), (2, 1)]) ∧
    ∃ F, PrimeField.new 5 = .built F ∧
      (⟨F, "x"⟩ : PolynomialRing PrimeField).multiply PrimeField.field.toCoefficientRing
        Limits.default (residuePoly [(0, 1), (1, 1)]) (residuePoly [(0, 4), (1, 1)]) =
        .value (residuePoly [(0, 4), (2, 1)])

/-- One implementation, negative (POL-R10): over `𝔽_2`, the same power gives
`(x + 1)² = x² + 1`, and the cross term `2x` leaves no term. -/
def CrossTermsVanishModuloTwo : Prop :=
  ∃ F, PrimeField.new 2 = .built F ∧
    (⟨F, "x"⟩ : PolynomialRing PrimeField).power PrimeField.field.toCoefficientRing
      Limits.default (residuePoly [(0, 1), (1, 1)]) 2 = .value (residuePoly [(0, 1), (2, 1)])

/-! ## Arithmetic against an independent reference (POL-R11) -/

/-- Arithmetic, positive (POL-R11): the coefficients of `(x + 1)⁴` are the
binomial coefficients 1, 4, 6, 4 and 1. -/
def BinomialCoefficientsOfAFourthPower : Prop :=
  (ratRing "x").power rationalRing Limits.default (ratPoly [(0, 1), (1, 1)]) 4 =
    .value (ratPoly ((List.range 5).map fun k => (k, (Nat.choose 4 k : ℚ))))

/-- Arithmetic, negative (POL-R11): `x (x + 1)` is `x² + x`, not `x² + 1`. -/
def ProductOfXAndXPlusOne : Prop :=
  let r := ratRing "x"
  r.multiply rationalRing Limits.default (ratPoly [(1, 1)]) (ratPoly [(0, 1), (1, 1)]) =
      .value (ratPoly [(1, 1), (2, 1)]) ∧
    r.multiply rationalRing Limits.default (ratPoly [(1, 1)]) (ratPoly [(0, 1), (1, 1)]) ≠
      .value (ratPoly [(0, 1), (2, 1)])

/-! ## Division with remainder (FLD-R08) -/

/-- Division with remainder, positive (FLD-R08): `x² ÷ (x - 1)` gives the
quotient `x + 1` and the remainder 1, over `ℚ` and over `𝔽_7`, where
`x - 1 = x + 6`. -/
def DivisionsWithRemainder : Prop :=
  Poly.divRem Rationals.field ⟨⟩ (ratPoly [(2, 1)]) (ratPoly [(0, -1), (1, 1)]) =
      .value (ratPoly [(0, 1), (1, 1)], ratPoly [(0, 1)]) ∧
    ∃ F, PrimeField.new 7 = .built F ∧
      Poly.divRem PrimeField.field F (residuePoly [(2, 1)]) (residuePoly [(0, 6), (1, 1)]) =
        .value (residuePoly [(0, 1), (1, 1)], residuePoly [(0, 1)])

/-- Division with remainder, negative (FLD-R08): `x ÷ 0` and the remainder of
`x` by 0 fail with `DivisionByZero`; and `1 ÷ x` gives the quotient 0 and the
remainder 1. -/
def DivisionByZeroAndByAHigherDegree : Prop :=
  Poly.divRem Rationals.field ⟨⟩ (ratPoly [(1, 1)]) Poly.zero = .fault (.field .divisionByZero) ∧
    Poly.rem Rationals.field ⟨⟩ (ratPoly [(1, 1)]) Poly.zero = .fault (.field .divisionByZero) ∧
    Poly.divRem Rationals.field ⟨⟩ (ratPoly [(0, 1)]) (ratPoly [(1, 1)]) =
      .value (Poly.zero, ratPoly [(0, 1)])

/-! ## Monic GCDs (FLD-R09) -/

/-- Monic GCDs, positive (FLD-R09): over `ℚ`,
`gcd(x² - 1, x - 1) = x - 1` and `gcd(x² - 1, x² - 2x + 1) = x - 1`. -/
def GcdsOfCommonFactors : Prop :=
  Poly.monicGcd Rationals.field ⟨⟩ (ratPoly [(0, -1), (2, 1)]) (ratPoly [(0, -1), (1, 1)]) =
      .value (ratPoly [(0, -1), (1, 1)]) ∧
    Poly.monicGcd Rationals.field ⟨⟩ (ratPoly [(0, -1), (2, 1)])
      (ratPoly [(0, 1), (1, -2), (2, 1)]) = .value (ratPoly [(0, -1), (1, 1)])

/-- Monic GCDs, negative (FLD-R09): `gcd(2x + 2, 0) = x + 1`, monic, not
`2x + 2`; `gcd(0, 0) = 0`; and `gcd(x, 3) = 1`. -/
def GcdsWithZeroAndConstants : Prop :=
  Poly.monicGcd Rationals.field ⟨⟩ (ratPoly [(0, 2), (1, 2)]) Poly.zero =
      .value (ratPoly [(0, 1), (1, 1)]) ∧
    Poly.monicGcd Rationals.field ⟨⟩ (ratPoly [(0, 2), (1, 2)]) Poly.zero ≠
      .value (ratPoly [(0, 2), (1, 2)]) ∧
    Poly.monicGcd Rationals.field ⟨⟩ Poly.zero Poly.zero = .value Poly.zero ∧
    Poly.monicGcd Rationals.field ⟨⟩ (ratPoly [(1, 1)]) (ratPoly [(0, 3)]) =
      .value (ratPoly [(0, 1)])

/-! ## Extended GCD (POL-R12) -/

/-- Extended GCD, positive (POL-R12): `gcdex(x² - 1, x - 1) = (0, 1, x - 1)`,
the cofactors of lowest degree, since `x - 1` is the GCD itself. -/
def ExtendedGcdOfAMultiple : Prop :=
  Poly.extendedGcd Rationals.field ⟨⟩ (ratPoly [(0, -1), (2, 1)]) (ratPoly [(0, -1), (1, 1)]) =
    .value ⟨Poly.zero, ratPoly [(0, 1)], ratPoly [(0, -1), (1, 1)]⟩

/-- Extended GCD, negative (POL-R12): `gcdex(0, 0) = (0, 0, 0)`, and
`gcdex(2x, 0) = (1/2, 0, x)`, with a monic GCD and a zero right cofactor. -/
def ExtendedGcdsWithZero : Prop :=
  Poly.extendedGcd Rationals.field ⟨⟩ Poly.zero Poly.zero =
      .value ⟨Poly.zero, Poly.zero, Poly.zero⟩ ∧
    Poly.extendedGcd Rationals.field ⟨⟩ (ratPoly [(1, 2)]) Poly.zero =
      .value ⟨ratPoly [(0, 1 / 2)], Poly.zero, ratPoly [(1, 1)]⟩

/-! ## Modular powers (POL-R13) -/

/-- Modular powers, positive (POL-R13): over `ℚ`, `x⁵ mod (x² + 1) = x`. -/
def ModularPowerOfX : Prop :=
  Poly.powerMod Rationals.field ⟨⟩ (ratPoly [(1, 1)]) 5 (ratPoly [(0, 1), (2, 1)]) =
    .value (ratPoly [(1, 1)])

/-- Modular powers, negative (POL-R13): a modulus 0 fails with
`DivisionByZero`; and modulo the constant 3, every canonical polynomial to
every power, the power 0 included, is the zero polynomial. -/
def ModularPowersByZeroAndConstants : Prop :=
  Poly.powerMod Rationals.field ⟨⟩ (ratPoly [(1, 1)]) 5 Poly.zero =
      .fault (.field .divisionByZero) ∧
    ∀ (a : Poly Fraction) (k : ℕ), a.Canonical Rationals.model ⟨⟩ →
      Poly.powerMod Rationals.field ⟨⟩ a k (ratPoly [(0, 3)]) = .value Poly.zero

/-! ## Evaluation (POL-R14) -/

/-- Evaluation, positive (POL-R14): over `ℚ`, `x² + 1` has the value 5 at 2. -/
def EvaluationAtTwo : Prop :=
  Poly.eval rationalRing ⟨⟩ (ratPoly [(0, 1), (2, 1)]) (Fraction.ofRat 2) =
    .value (Fraction.ofRat 5)

/-- Evaluation, negative (POL-R14): over `𝔽_7`, `x⁷ - x` has the value 0 at
each of the 7 elements, and it is not the zero polynomial. -/
def EvaluationVanishesOnAllOfSeven : Prop :=
  ∃ F, PrimeField.new 7 = .built F ∧
    (∀ c, c < 7 →
      Poly.eval PrimeField.field.toCoefficientRing F (residuePoly [(1, 6), (7, 1)]) ⟨c⟩ =
        .value ⟨0⟩) ∧
    residuePoly [(1, 6), (7, 1)] ≠ Poly.zero

/-! ## Homomorphisms (FLD-R11) -/

/-- Maps of polynomials, positive (FLD-R11): the map of the integers into
`𝔽_7` takes `x² + 9` to `x² + 2`, and `7x + 1` to `1`, whose term of degree
1 has the image zero and leaves no term. -/
def IntegerPolynomialsReduceModuloSeven : Prop :=
  ∃ F, PrimeField.new 7 = .built F ∧
    Poly.map Integers.toPrimeField PrimeField.field.toCoefficientRing ⟨⟩ F ⟨[(0, 9), (2, 1)]⟩ =
      .value (.mapped (residuePoly [(0, 2), (2, 1)])) ∧
    Poly.map Integers.toPrimeField PrimeField.field.toCoefficientRing ⟨⟩ F ⟨[(0, 1), (1, 7)]⟩ =
      .value (.mapped (residuePoly [(0, 1)]))

/-- Maps of polynomials, negative (FLD-R11): the reduction of the rationals
into `𝔽_7` takes `x + 1/7` to the result state `notInDomain`, a value and not
an error. -/
def ReductionOutsideTheDomain : Prop :=
  ∃ F, PrimeField.new 7 = .built F ∧
    Poly.map Rationals.toPrimeField PrimeField.field.toCoefficientRing ⟨⟩ F
      (ratPoly [(0, 1 / 7), (1, 1)]) = .value .notInDomain

end Kalyx.Statements.Polynomials

end
