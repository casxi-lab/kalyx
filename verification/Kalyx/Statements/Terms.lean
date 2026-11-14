module

public import Kalyx.Spec.Terms.Condition
public import Kalyx.Spec.Terms.Canonical
public import Kalyx.Spec.Terms.Display
public import Kalyx.Spec.Terms.Eval
public import Kalyx.Spec.Terms.Semantics

/-!
# Statements about the term core

The registered statements of the specification of the term core
(`Kalyx.Spec.Terms`), each a proposition named here and proved, or to be
proved, by a theorem of `Kalyx.Proofs.Terms`. They are written from the
numbered requirements of the terms contract
(`docs/components/terms/contract.md`), whose table of requirements and
statements names, for each requirement, the statements that state it.

The first nine are the properties of the canonical forms: sums and products
do not depend on the order or the grouping of their operands; the
constructors return canonical terms, which rebuild into themselves; the order
of terms is total; merging adds coefficients and exponents; the constructors
keep the bases of negative powers, and the meaning of their inputs; the
faults of strict evaluation; when a comparison under `maxIntegerBits` may
report `ResourceLimit`; and calls are atoms. A property holds for every total
choice of the orders that are parameters (`Orders.Total`), for rules of calls
that return canonical terms and keep the bases of negative powers
(`RegistryRules.Closed`), and for every limit `maxExponent`, on operands that
are canonical under them (`Term.Canonical`).

The others are a positive and a negative example of each requirement. The
examples fix the parameters: the order `Orders.sample`, the rules
`RegistryRules.empty`, which keep every call, and the default limit
`defaultMaxExponent`, unless an example names another. Only conditions and
algebraic constants read the order parameters, and only calls read the
rules.
-/

@[expose] public section

namespace Kalyx.Statements.Terms

open Kalyx.Spec.Terms

/-! ## Notions of the statements -/

/-- A result of a construction that is canonical: a value that `canonical`
holds of, or a fault other than `Internal`, or `ResourceLimit`. -/
def CanonicalResult (canonical : Term → Prop) : Result Term → Prop
  | .value u => canonical u
  | .fault e => e ≠ .internal
  | .resourceLimit _ => True

/-- The total coefficient of the core `t` among the monomials `ms`. -/
def coefficientOf (t : Term) (ms : List (ℚ × Term)) : ℚ :=
  ((ms.filter fun m => m.2 = t).map Prod.fst).sum

/-- The total exponent of the key `K` among the items `(b, k)` of a product. -/
def exponentOf (K : Key) (items : List (Term × ℤ)) : ℤ :=
  ((items.filter fun x => Key.of x.1 x.2 = K).map Prod.snd).sum

/-- The canonical term of `i ^ k`, by `k` modulo 4: 1, `i`, `-1` and `-i`,
the product of `-1` and `i`. -/
def iPower (k : ℤ) : Term :=
  if k % 4 = 0 then .number 1
  else if k % 4 = 1 then Term.imaginaryUnit
  else if k % 4 = 2 then .number (-1)
  else .product (-1) [Term.imaginaryUnit]

/-- No term of `ts` holds a call of `piecewise`, of any number of
arguments. -/
def NoPiecewise (ts : List Term) : Prop := ∀ t ∈ ts, ∀ args, Term.call Head.piecewise args ∉ t.nodes

/-- The truth of every condition is defined wherever the meanings of its
operands are: `I.cond` gives `none` only for an operand that is undefined.
The conditions of kalyx do not all satisfy this law, since an ordered
comparison of values that are not real is undefined; a `piecewise` call
whose condition is undefined at a point where its operands are defined is
undefined there, and a construction that cancels such a call can be defined
at that point. -/
def CondDefined (I : Interp) : Prop :=
  ∀ s ms, (∀ m ∈ ms, m ≠ .value none ∧ m ≠ .truth none) → I.cond s ms ≠ none

/-- The meaning of the result `u` of a construction against the strict meaning
`f` of its input, whose operands are `ts`: when no operand holds `piecewise`,
the two are equal at every assignment; and under an interpretation whose
conditions are defined wherever their operands are, `u` is defined only where
`f` is, with the same value there (`DefinedWithin`). -/
def MeaningKept (I : Interp) (ts : List Term) (u : Term) (f : Assignment → Option ℂ) : Prop :=
  (NoPiecewise ts → ∀ ρ, u.denote I ρ = f ρ) ∧
    (CondDefined I → DefinedWithin (fun ρ => u.denote I ρ) f)

/-- Every call of the term `u` is a call of one of the terms `ts`, with the
same head and the same arguments. -/
def CallsWithin (u : Term) (ts : List Term) : Prop :=
  ∀ h args, Term.call h args ∈ u.nodes → ∃ t ∈ ts, Term.call h args ∈ t.nodes

/-! ## Properties -/

/-- Sums and products do not depend on the order or the grouping of their
operands (TRM-R01, TRM-R03, TRM-R04, TRM-R13, TRM-R14). On canonical
operands, two lists that are permutations of each other give the same sum,
and the same product, when both constructions succeed; and a list in which a
segment is replaced by its sum (its product) gives the same sum (product) as
the list itself, when the constructions succeed. A sum of values always
succeeds. A product of values fails only with `ResourceLimit` naming
`max_exponent`, and once it succeeds under a limit it gives the same term
under every larger limit. The effective bound on exponents is at most
`2⁶³ - 1`, so no limit lets every product succeed; and whether a product
succeeds under a limit may depend on the grouping, since the exponents of a
key are checked where they are added. -/
def SumsAndProductsIgnoreOrderAndGrouping : Prop :=
  ∀ (o : Orders) (maxExponent : ℕ) (R : RegistryRules), o.Total →
    R.Closed (fun me => Term.Canonical o me R) Term.negBases →
    let canonical := Term.Canonical o maxExponent R
    (∀ ts ts' u u', (∀ t ∈ ts, canonical t) → ts.Perm ts' →
      mkSum o ts = .value u → mkSum o ts' = .value u' → u = u') ∧
    (∀ ts₁ ts₂ ts₃ s u u', (∀ t ∈ ts₁ ++ ts₂ ++ ts₃, canonical t) →
      mkSum o ts₂ = .value s → mkSum o (ts₁ ++ ts₂ ++ ts₃) = .value u →
      mkSum o (ts₁ ++ s :: ts₃) = .value u' → u = u') ∧
    (∀ ts ts' u u', (∀ t ∈ ts, canonical t) → ts.Perm ts' →
      mkProduct o maxExponent ts = .value u → mkProduct o maxExponent ts' = .value u' →
      u = u') ∧
    (∀ ts₁ ts₂ ts₃ s u u', (∀ t ∈ ts₁ ++ ts₂ ++ ts₃, canonical t) →
      mkProduct o maxExponent ts₂ = .value s →
      mkProduct o maxExponent (ts₁ ++ ts₂ ++ ts₃) = .value u →
      mkProduct o maxExponent (ts₁ ++ s :: ts₃) = .value u' → u = u') ∧
    (∀ ts : List Term, (∀ t ∈ ts, t.isCondition = false) → ∃ u, mkSum o ts = .value u) ∧
    (∀ ts : List Term, (∀ t ∈ ts, canonical t ∧ t.isCondition = false) →
      (∃ u, mkProduct o maxExponent ts = .value u) ∨
        mkProduct o maxExponent ts = .resourceLimit .exponent) ∧
    ∀ ts u me, mkProduct o maxExponent ts = .value u → maxExponent ≤ me →
      mkProduct o me ts = .value u

/-- The constructors return canonical terms, and a canonical term rebuilds
into itself (TRM-R02, TRM-R05, TRM-R06, TRM-R13 to TRM-R15). On canonical
operands, every constructor of the term core, the sum, the product, the
power, the negation, the difference, the quotient, the condition and the
symbol, returns a canonical term or fails with a fault other than `Internal`
or with `ResourceLimit`; the call constructor returns a canonical term or
fails, and fails with `Internal` only where the rules do. A canonical term
whose exponents the limit admits is rebuilt from its parts through the
constructors into itself (`Term.rebuild`). -/
def CanonicalFormsAreClosedAndIdempotent : Prop :=
  ∀ (o : Orders) (maxExponent : ℕ) (R : RegistryRules), o.Total →
    R.Closed (fun me => Term.Canonical o me R) Term.negBases →
    let canonical := Term.Canonical o maxExponent R
    let built := CanonicalResult canonical
    (∀ ts, (∀ t ∈ ts, canonical t) → built (mkSum o ts)) ∧
    (∀ ts, (∀ t ∈ ts, canonical t) → built (mkProduct o maxExponent ts)) ∧
    (∀ b k, canonical b → built (mkPower o maxExponent b k)) ∧
    (∀ t, canonical t → built (mkNegate o maxExponent t)) ∧
    (∀ a b, canonical a → canonical b → built (mkSubtract o maxExponent a b)) ∧
    (∀ a b, canonical a → canonical b → built (mkDivide o maxExponent a b)) ∧
    (∀ s ops, (∀ t ∈ ops, canonical t) → built (mkCondition s ops)) ∧
    (∀ name, built (mkSymbol name)) ∧
    (∀ h args, (∀ a ∈ args, canonical a) →
      (∀ u, mkCall maxExponent R h args = .value u → canonical u) ∧
      (mkCall maxExponent R h args = .fault .internal →
        R.apply maxExponent h args = .fault .internal)) ∧
    ∀ t, canonical t → t.exponentsWithin maxExponent = true →
      t.rebuild o maxExponent R = .value t

/-- The order of terms is total (TRM-R01, TRM-R03, TRM-R13 to TRM-R15): for
every total choice of the order parameters, `Term.cmp` and the order of the
keys of factors are total orders, oriented, transitive, and `eq` exactly for
equal arguments; and terms of different ranks are ordered by rank, so
numbers, constants, symbols, calls, powers, products, sums and conditions
come in this order. -/
def TermOrderIsTotal : Prop :=
  ∀ o : Orders, o.Total →
    TotalCmp (Term.cmp o) ∧ TotalCmp (Key.cmp o) ∧
      ∀ s t, s.rank < t.rank → Term.cmp o s t = .lt

/-- Merging adds coefficients and exponents (TRM-R04, TRM-R05, TRM-R13). On
canonical operands:

* the sum keeps the constant of its operands and, for every core, their
  total coefficient, the parts read from the result as `sumParts` reads an
  operand; its monomials with the coefficient 0 are at most the witness
  monomial over the maximal elements of the bases that the cores of total 0
  hold with a negative exponent and the other cores do not;
* the product of operands whose items are neither `i` nor roots of a
  literal degree, with a coefficient other than 0, keeps the coefficient and,
  for every key, the total exponent of its operands; a constant has one key
  for both signs;
* the product with the coefficient 0 is the zero witness of the maximal
  elements of the bases of its operands;
* a one `(b⁻¹)⁰` whose base the other operands hold with a negative
  exponent does not change the product;
* `i ^ k` is `i` to the power `k` modulo 4, the sign in the coefficient;
* for a root `ⁿ√u` of a literal degree `n` and `k ≥ n`,
  `(ⁿ√u)ᵏ = u ^ ⌊k/n⌋ (ⁿ√u) ^ (k mod n)` when both sides succeed. -/
def MergingAddsCoefficientsAndExponents : Prop :=
  ∀ (o : Orders) (maxExponent : ℕ) (R : RegistryRules), o.Total →
    R.Closed (fun me => Term.Canonical o me R) Term.negBases →
    let canonical := Term.Canonical o maxExponent R
    (∀ ts u, (∀ t ∈ ts, canonical t) → mkSum o ts = .value u →
      let ms := (sumParts ts).2
      let cancelled := ms.filter fun m => coefficientOf m.2 ms = 0
      let kept := ms.filter fun m => coefficientOf m.2 ms ≠ 0
      let bs := maxBases o (uncovered (Term.negBasesPairs cancelled) (Term.negBasesPairs kept))
      (sumParts [u]).1 = (sumParts ts).1 ∧
        (∀ t, coefficientOf t (sumParts [u]).2 = coefficientOf t ms) ∧
        (sumParts [u]).2.filter (fun m => m.1 = 0) =
          if bs = [] then [] else [(0, witnessCore bs)]) ∧
    (∀ ts u p q, (∀ t ∈ ts, canonical t) → productParts maxExponent ts = .value p →
      (∀ x ∈ p.items, x.1 ≠ Term.imaginaryUnit ∧ rootOf x.1 = none) → p.coefficient ≠ 0 →
      mkProduct o maxExponent ts = .value u → productParts maxExponent [u] = .value q →
      q.coefficient = p.coefficient ∧ ∀ K, exponentOf K q.items = exponentOf K p.items) ∧
    (∀ ts u, (∀ t ∈ ts, canonical t) → mkProduct o maxExponent (.number 0 :: ts) = .value u →
      u = zeroWitness (maxBases o (Term.negBasesList ts))) ∧
    (∀ b ts, (∀ t ∈ ts, canonical t) → b ∈ Term.negBasesList ts →
      mkProduct o maxExponent (b.oneOf :: ts) = mkProduct o maxExponent ts) ∧
    (∀ k, k.natAbs ≤ exponentBound maxExponent →
      mkPower o maxExponent Term.imaginaryUnit k = .value (iPower k)) ∧
    ∀ s u n k v w, canonical s → rootOf s = some (u, n) → (n : ℤ) ≤ k →
      mkPower o maxExponent s k = .value v →
      (do
        let a ← mkPower o maxExponent u (k / n)
        let b ← mkPower o maxExponent s (k % n)
        mkProduct o maxExponent [a, b] : Result Term) = .value w →
      v = w

/-- The constructors keep the bases of negative powers (TRM-R05, TRM-R06,
TRM-R13, TRM-R14), the structural form of the negative-exponent invariant.
On canonical operands, `N` of every operand is contained in `N` of the
result of the sum, the product, the power, the negation, the difference, the
quotient and the call, except the rule of `piecewise` on a truth value,
which selects a branch; the bases that a negative power introduces, of the
base of a power with a negative exponent and of the divisor of a quotient
(`Term.introducedBases`), are in `N` of the result; `hasNegativePower` holds
exactly when `N` is not empty; and the witnesses name the maximal elements of
the bases they keep: `t - t` is the zero witness of the maximal elements of
`N(t)`, and `t ^ 0` for a value `t` that is not a number is 1 or the ones of
the maximal elements of `N(t)` (`powerZero`). -/
def ConstructorsKeepNegativeBases : Prop :=
  ∀ (o : Orders) (maxExponent : ℕ) (R : RegistryRules), o.Total →
    R.Closed (fun me => Term.Canonical o me R) Term.negBases →
    let canonical := Term.Canonical o maxExponent R
    (∀ ts u, (∀ t ∈ ts, canonical t) → mkSum o ts = .value u → BasesKept ts u) ∧
    (∀ ts u, (∀ t ∈ ts, canonical t) → mkProduct o maxExponent ts = .value u →
      BasesKept ts u) ∧
    (∀ b k u, canonical b → mkPower o maxExponent b k = .value u → BasesKept [b] u) ∧
    (∀ t u, canonical t → mkNegate o maxExponent t = .value u → BasesKept [t] u) ∧
    (∀ a b u, canonical a → canonical b → mkSubtract o maxExponent a b = .value u →
      BasesKept [a, b] u) ∧
    (∀ a b u, canonical a → canonical b → mkDivide o maxExponent a b = .value u →
      BasesKept [a, b] u) ∧
    (∀ h args u, (∀ a ∈ args, canonical a) → (h = Head.piecewise → piecewiseBranch args = none) →
      mkCall maxExponent R h args = .value u → BasesKept args u) ∧
    (∀ b k u, canonical b → k < 0 → mkPower o maxExponent b k = .value u →
      ∀ c ∈ b.introducedBases, c ∈ u.negBases) ∧
    (∀ a b u, canonical a → canonical b → mkDivide o maxExponent a b = .value u →
      ∀ c ∈ b.introducedBases, c ∈ u.negBases) ∧
    (∀ t : Term, t.hasNegativePower = true ↔ t.negBases ≠ []) ∧
    (∀ t u, canonical t → mkSubtract o maxExponent t t = .value u →
      u = zeroWitness (maxBases o t.negBases)) ∧
    ∀ t : Term, t.isCondition = false → (∀ q, t ≠ .number q) →
      mkPower o maxExponent t 0 = .value (powerZero o t)

/-- The constructors keep the meaning of their inputs (TRM-R04 to TRM-R06,
TRM-R13 to TRM-R15), the semantic form of the negative-exponent invariant.
The meaning of a term is a partial function from assignments to the complex
numbers (`Term.denote`). Under an interpretation whose laws hold
(`Interp.Lawful`: the truth values, the identities of roots, nonzero values of
valid constants), for rules of calls that keep the meaning of a call
(`RegistryRules.Keeps`), on canonical operands, the result of the sum, the
product, the power, the negation, the difference and the quotient has the
strict meaning of its input at every assignment when no operand holds
`piecewise`; and, where the truth of every condition is defined wherever its
operands are (`CondDefined`), it is defined only where its input is, with the
same value, so it gives no value where its input is undefined. A call
constructed by the call constructor has the meaning of the call at every
assignment. -/
def ConstructorsKeepMeanings : Prop :=
  ∀ (o : Orders) (maxExponent : ℕ) (R : RegistryRules) (I : Interp), o.Total →
    R.Closed (fun me => Term.Canonical o me R) Term.negBases →
    R.Keeps (fun t ρ => t.denote I ρ) → I.Lawful →
    let canonical := Term.Canonical o maxExponent R
    (∀ ts u, (∀ t ∈ ts, canonical t) → mkSum o ts = .value u →
      MeaningKept I ts u fun ρ => (Term.denoteList I ρ ts).map List.sum) ∧
    (∀ ts u, (∀ t ∈ ts, canonical t) → mkProduct o maxExponent ts = .value u →
      MeaningKept I ts u fun ρ => (Term.denoteList I ρ ts).map List.prod) ∧
    (∀ b k u, canonical b → mkPower o maxExponent b k = .value u →
      MeaningKept I [b] u fun ρ => (b.denote I ρ).bind fun v => zpowMeaning v k) ∧
    (∀ t u, canonical t → mkNegate o maxExponent t = .value u →
      MeaningKept I [t] u fun ρ => (t.denote I ρ).map fun v => -v) ∧
    (∀ a b u, canonical a → canonical b → mkSubtract o maxExponent a b = .value u →
      MeaningKept I [a, b] u fun ρ =>
        (a.denote I ρ).bind fun v => (b.denote I ρ).map fun w => v - w) ∧
    (∀ a b u, canonical a → canonical b → mkDivide o maxExponent a b = .value u →
      MeaningKept I [a, b] u fun ρ =>
        (a.denote I ρ).bind fun v => (b.denote I ρ).bind fun w =>
          (zpowMeaning w (-1)).map fun r => v * r) ∧
    ∀ h args u, (∀ a ∈ args, canonical a) → mkCall maxExponent R h args = .value u →
      ∀ ρ, u.denote I ρ = (Term.call h args).denote I ρ

/-- The faults of strict evaluation (TRM-R05 to TRM-R07), under an explicit
`maxExponent`:

* an exponent beyond the effective bound makes the power fail with
  `ResourceLimit` naming `max_exponent` before anything else, whatever its
  base; so does the sum of the exponents of one key in a product, and the
  product of the exponents of a power of a power that merges;
* after that check, the power of a canonical base fails with
  `DivisionByZero` exactly for a negative exponent and a base that is the
  number 0 or a product with the coefficient 0, and the quotient exactly for
  such a divisor; sums and products never fail with it;
* where a power or a quotient fails with `DivisionByZero`, the base or the
  divisor raised to its exponent is undefined at every assignment;
* `0⁰ = 1`, and `t⁰ = 1` for a value `t` without negative powers. -/
def StrictEvaluationFaults : Prop :=
  ∀ (o : Orders) (maxExponent : ℕ) (R : RegistryRules), o.Total →
    let canonical := Term.Canonical o maxExponent R
    (∀ (b : Term) (k : ℤ), exponentBound maxExponent < k.natAbs →
      mkPower o maxExponent b k = .resourceLimit .exponent) ∧
    (∀ b j k, 0 < j * k → exponentBound maxExponent < (j + k).natAbs →
      mkProduct o maxExponent [.power b j, .power b k] = .resourceLimit .exponent) ∧
    (∀ b j k, k ≠ 0 → k ≠ 1 → mergeCondition j k = true →
      exponentBound maxExponent < (j * k).natAbs →
      mkPower o maxExponent (.power b j) k = .resourceLimit .exponent) ∧
    (∀ b k, canonical b → k.natAbs ≤ exponentBound maxExponent →
      (mkPower o maxExponent b k = .fault .divisionByZero ↔
        k < 0 ∧ (b = .number 0 ∨ ∃ fs, b = .product 0 fs))) ∧
    (∀ a b, canonical a → canonical b → 1 ≤ maxExponent →
      (mkDivide o maxExponent a b = .fault .divisionByZero ↔
        b = .number 0 ∨ ∃ fs, b = .product 0 fs)) ∧
    (∀ ts, mkSum o ts ≠ .fault .divisionByZero) ∧
    (∀ ts, mkProduct o maxExponent ts ≠ .fault .divisionByZero) ∧
    (∀ (I : Interp) b k, mkPower o maxExponent b k = .fault .divisionByZero →
      ∀ ρ, (b.denote I ρ).bind (fun v => zpowMeaning v k) = none) ∧
    (∀ (I : Interp) a b, mkDivide o maxExponent a b = .fault .divisionByZero →
      ∀ ρ, (b.denote I ρ).bind (fun v => zpowMeaning v (-1)) = none) ∧
    mkPower o maxExponent (.number 0) 0 = .value (.number 1) ∧
    ∀ t : Term, t.isCondition = false → t.negBases = [] →
      mkPower o maxExponent t 0 = .value (.number 1)

/-- When a comparison under `maxIntegerBits` may report `ResourceLimit`
(TRM-R03, TRM-R08), with the limit explicit: the comparison never fails with
a fault; a value is the order of terms; equal terms compare `eq` under every
limit; `ResourceLimit` names `max_integer_bits`, and only where the first
difference of the walk of the two terms is a pair of different rationals
`a/b` and `c/d` with `max(|a| + |d|, |c| + |b|)` above the limit; and where no
such pair is above the limit, the comparison is the order of terms. Which of
the fast paths of the numbers avoid the cross products is not stated. -/
def ComparisonUnderBitLimit : Prop :=
  ∀ (o : Orders) (maxIntegerBits : ℕ) (s t : Term), o.Total →
    (∀ e, Term.compareAt o maxIntegerBits s t ≠ .fault e) ∧
    (∀ r, Term.compareAt o maxIntegerBits s t = .value r → r = Term.cmp o s t) ∧
    (s = t → Term.compareAt o maxIntegerBits s t = .value .eq) ∧
    (∀ f, Term.compareAt o maxIntegerBits s t = .resourceLimit f →
      f = .integerBits ∧ ∃ a b, Term.firstDifference o s t = .rationals a b ∧ a ≠ b ∧
        maxIntegerBits < ratCrossBound a b) ∧
    ((∀ a b, Term.firstDifference o s t = .rationals a b → ratCrossBound a b ≤ maxIntegerBits) →
      Term.compareAt o maxIntegerBits s t = .value (Term.cmp o s t))

/-- Calls are atoms of sums, products and powers (TRM-R04, TRM-R14). On
canonical operands, every call of the result of a sum, a product or a power
is a call of an operand with the same arguments, so these constructors never
enter, rewrite or create a call, and a result of operands without calls has
none; the powers of roots only remove calls or keep them. A call merges as
one with an equal call, `c c = c ^ 2` and `c + c = 2 c`, and stays apart
from a different call, in the order of terms. -/
def CallsAreAtoms : Prop :=
  ∀ (o : Orders) (maxExponent : ℕ) (R : RegistryRules), o.Total →
    R.Closed (fun me => Term.Canonical o me R) Term.negBases →
    let canonical := Term.Canonical o maxExponent R
    (∀ ts u, (∀ t ∈ ts, canonical t) → mkSum o ts = .value u → CallsWithin u ts) ∧
    (∀ ts u, (∀ t ∈ ts, canonical t) → mkProduct o maxExponent ts = .value u →
      CallsWithin u ts) ∧
    (∀ b k u, canonical b → mkPower o maxExponent b k = .value u → CallsWithin u [b]) ∧
    (∀ h args, canonical (.call h args) →
      mkProduct o maxExponent [.call h args, .call h args] =
        mkPower o maxExponent (.call h args) 2 ∧
      mkSum o [.call h args, .call h args] = .value (.product 2 [.call h args])) ∧
    ∀ h args g brgs, canonical (.call h args) → canonical (.call g brgs) →
      Term.call h args ≠ .call g brgs → 1 ≤ maxExponent →
      mkProduct o maxExponent [.call h args, .call g brgs] =
        .value (.product 1 (sortBy (Term.cmp o) [.call h args, .call g brgs])) ∧
      mkSum o [.call h args, .call g brgs] =
        .value (.sum 0 (sortBy (monomialCmp o) [(1, .call h args), (1, .call g brgs)]))

/-! ## Uniqueness (TRM-R01) -/

/-- Uniqueness, positive (TRM-R01): with `s = x + y`, `a = 2 s` and `b = -s`,
the sums `a + b + b` and `(a + b) + b` are both 0, `a + b + a + b` and
`(a + b) + (a + b)` are both `2 x + 2 y`, and `s - s` is 0, whose power `-1`
fails with `DivisionByZero`. -/
def ScaledCopiesOfOneSumMergeInEveryGrouping : Prop :=
  let o := Orders.sample
  let me := defaultMaxExponent
  let x : Term := .symbol "x"
  let y : Term := .symbol "y"
  let s : Term := .sum 0 [(1, x), (1, y)]
  let a : Term := .sum 0 [(2, x), (2, y)]
  let b : Term := .sum 0 [(-1, x), (-1, y)]
  mkSum o [x, y] = .value s ∧ mkProduct o me [.number 2, s] = .value a ∧
    mkNegate o me s = .value b ∧
    mkSum o [a, b, b] = .value (.number 0) ∧
    (mkSum o [a, b]).bind (fun ab => mkSum o [ab, b]) = .value (.number 0) ∧
    mkSum o [a, b, a, b] = .value a ∧
    (mkSum o [a, b]).bind (fun ab => mkSum o [ab, ab]) = .value a ∧
    (mkSubtract o me s s).bind (fun d => mkPower o me d (-1)) = .fault .divisionByZero

/-- Uniqueness, negative (TRM-R01): opposite signs never merge, in any
grouping: `(x x⁻²) x²` and `x (x⁻² x²)` are both `x³ x⁻²`, and not `x`. -/
def OppositeSignsNeverMergeInAnyGrouping : Prop :=
  let o := Orders.sample
  let me := defaultMaxExponent
  let x : Term := .symbol "x"
  let p : Term := .product 1 [.power x 3, .power x (-2)]
  (mkProduct o me [x, .power x (-2)]).bind (fun l => mkProduct o me [l, .power x 2]) =
      .value p ∧
    (mkProduct o me [.power x (-2), .power x 2]).bind (fun r => mkProduct o me [x, r]) =
      .value p ∧
    p ≠ x

/-! ## Idempotence (TRM-R02) -/

/-- Idempotence, positive (TRM-R02): a content that cancels against a
coefficient leaves no product, `½ (2 x + 2 y) = x + y` and
`(1 - x)² = (x - 1)²`; and `x + y` is canonical and is rebuilt from its parts
into itself. -/
def ContentThatCancelsLeavesNoProduct : Prop :=
  let o := Orders.sample
  let me := defaultMaxExponent
  let x : Term := .symbol "x"
  let y : Term := .symbol "y"
  let s : Term := .sum 0 [(1, x), (1, y)]
  mkProduct o me [.number (1 / 2), .sum 0 [(2, x), (2, y)]] = .value s ∧
    (mkSubtract o me (.number 1) x).bind (fun d => mkPower o me d 2) =
      (mkSubtract o me x (.number 1)).bind (fun d => mkPower o me d 2) ∧
    Term.Canonical o me RegistryRules.empty s ∧
    s.rebuild o me RegistryRules.empty = .value s

/-- Idempotence, negative (TRM-R02): three hand-written nodes are not
canonical: a product with the coefficient 1 and a single factor, a monomial
whose core is a sum, and the sum `2 x + 2 y`, which is not primitive, as a
factor. -/
def NonCanonicalNodesFailTheShape : Prop :=
  let o := Orders.sample
  let me := defaultMaxExponent
  let x : Term := .symbol "x"
  let y : Term := .symbol "y"
  let z : Term := .symbol "z"
  ¬Term.Canonical o me RegistryRules.empty (.product 1 [x]) ∧
    ¬Term.Canonical o me RegistryRules.empty (.sum 1 [(2, .sum 0 [(1, x), (1, y)])]) ∧
    ¬Term.Canonical o me RegistryRules.empty (.product 1 [z, .sum 0 [(2, x), (2, y)]])

/-! ## Order of terms in sums and products (TRM-R03) -/

/-- Order in sums and products, positive (TRM-R03): `y + x` and `x + y` are
both `x + y`, and `y x` is `x y`; and of two names of which one is a prefix of
the other, the prefix comes first: `xy + x` is `x + xy`. -/
def SumsAndProductsSortTheirTerms : Prop :=
  let o := Orders.sample
  let me := defaultMaxExponent
  let x : Term := .symbol "x"
  let y : Term := .symbol "y"
  mkSum o [y, x] = .value (.sum 0 [(1, x), (1, y)]) ∧
    mkSum o [x, y] = .value (.sum 0 [(1, x), (1, y)]) ∧
    mkProduct o me [y, x] = .value (.product 1 [x, y]) ∧
    mkSum o [.symbol "xy", x] = .value (.sum 0 [(1, x), (1, .symbol "xy")])

/-- Order in sums and products, negative (TRM-R03): a hand-written sum whose
cores decrease is not canonical; and symbols are ordered by the bytes of their
names, so `B` comes before `a`, unlike in the order of the alphabet. -/
def UnsortedCoresAndTheByteOrder : Prop :=
  let o := Orders.sample
  let me := defaultMaxExponent
  let x : Term := .symbol "x"
  let y : Term := .symbol "y"
  ¬Term.Canonical o me RegistryRules.empty (.sum 0 [(1, y), (1, x)]) ∧
    Term.cmp o (.symbol "B") (.symbol "a") = .lt ∧
    mkSum o [.symbol "a", .symbol "B"] = .value (.sum 0 [(1, .symbol "B"), (1, .symbol "a")])

/-! ## Merging of like terms and coefficients (TRM-R04) -/

/-- Merging, positive (TRM-R04): cores and bases are compared by structure,
and a sum among the factors by its primitive part, so
`2 z (x + y) + 3 z (y + x) = 5 z (x + y)` and
`(2 x + 2 y) (y + x) = 2 (x + y)²`. -/
def LikeTermsAndCoefficientsMerge : Prop :=
  let o := Orders.sample
  let me := defaultMaxExponent
  let x : Term := .symbol "x"
  let y : Term := .symbol "y"
  let z : Term := .symbol "z"
  let s : Term := .sum 0 [(1, x), (1, y)]
  (do
      let t ← mkSum o [y, x]
      let a ← mkProduct o me [.number 2, z, s]
      let b ← mkProduct o me [.number 3, z, t]
      mkSum o [a, b] : Result Term) = .value (.product 5 [z, s]) ∧
    (mkSum o [y, x]).bind (fun t => mkProduct o me [.sum 0 [(2, x), (2, y)], t]) =
      .value (.product 2 [.power s 2])

/-- Merging, negative (TRM-R04): factors of one base with exponents of
opposite signs have different keys and do not merge: `x² x⁻¹` and `x x⁻¹`
keep both factors, and `x² x⁻¹` is not `x`. -/
def OppositeSignsKeepTwoFactors : Prop :=
  let o := Orders.sample
  let me := defaultMaxExponent
  let x : Term := .symbol "x"
  mkProduct o me [.power x 2, .power x (-1)] = .value (.product 1 [.power x 2, .power x (-1)]) ∧
    mkProduct o me [x, .power x (-1)] = .value (.product 1 [x, .power x (-1)]) ∧
    mkProduct o me [.power x 2, .power x (-1)] ≠ .value x

/-! ## Elimination of 0 and 1 (TRM-R05) -/

/-- Elimination of 0 and 1, positive (TRM-R05): `x + 0`, `1 x` and `x¹` are
`x`; `x - x` is 0; the empty sum is 0 and the empty product 1. -/
def ZeroAndOneDisappear : Prop :=
  let o := Orders.sample
  let me := defaultMaxExponent
  let x : Term := .symbol "x"
  mkSum o [x, .number 0] = .value x ∧ mkProduct o me [.number 1, x] = .value x ∧
    mkPower o me x 1 = .value x ∧ mkSubtract o me x x = .value (.number 0) ∧
    mkSum o [] = .value (.number 0) ∧ mkProduct o me [] = .value (.number 1)

/-- Elimination of 0 and 1, negative (TRM-R05): a base that occurs with a
negative exponent keeps a witness: `x⁻¹ - x⁻¹` is `0 x⁻¹`, not 0;
`5 + x⁻¹ - x⁻¹` is `5 + 0 x⁻¹`; and `(x⁻¹)⁰` stays, not 1. -/
def WitnessesKeepCancelledBases : Prop :=
  let o := Orders.sample
  let me := defaultMaxExponent
  let x : Term := .symbol "x"
  let r : Term := .power x (-1)
  mkSubtract o me r r = .value (.product 0 [r]) ∧
    mkSubtract o me r r ≠ .value (.number 0) ∧
    (mkSum o [.number 5, r]).bind (fun s => mkSubtract o me s r) = .value (.sum 5 [(0, r)]) ∧
    mkPower o me r 0 = .value (.power r 0) ∧
    mkPower o me r 0 ≠ .value (.number 1)

/-! ## Integer powers and the negative-exponent invariant (TRM-R06) -/

/-- Integer powers, positive (TRM-R06): `x⁻¹ x⁻² = x⁻³`, `(x⁻¹)² = x⁻²`,
`(x²)⁻¹ = x⁻²` and `(x²)³ = x⁶`; a sum base is taken by its primitive part,
`(2 x + 2 y)² = 4 (x + y)²`; and `N(x / x)` is `{x}`. -/
def PowersMergeAndDistribute : Prop :=
  let o := Orders.sample
  let me := defaultMaxExponent
  let x : Term := .symbol "x"
  let y : Term := .symbol "y"
  mkProduct o me [.power x (-1), .power x (-2)] = .value (.power x (-3)) ∧
    mkPower o me (.power x (-1)) 2 = .value (.power x (-2)) ∧
    mkPower o me (.power x 2) (-1) = .value (.power x (-2)) ∧
    mkPower o me (.power x 2) 3 = .value (.power x 6) ∧
    mkPower o me (.sum 0 [(2, x), (2, y)]) 2 =
      .value (.product 4 [.power (.sum 0 [(1, x), (1, y)]) 2]) ∧
    (mkDivide o me x x).map Term.negBases = .value [x]

/-- Integer powers, negative (TRM-R06): a power of a power that would lose a
base with a negative exponent stays as written, `(x⁻¹)⁻¹` and `(x⁻²)⁻³`; and
a zero witness keeps a sum base by its primitive part, so `N` does not shrink:
`0 (2 x + 2 y)⁻¹ = 0 (x + y)⁻¹`. -/
def PowersThatWouldHideBasesStay : Prop :=
  let o := Orders.sample
  let me := defaultMaxExponent
  let x : Term := .symbol "x"
  let y : Term := .symbol "y"
  mkPower o me (.power x (-1)) (-1) = .value (.power (.power x (-1)) (-1)) ∧
    mkPower o me (.power x (-2)) (-3) = .value (.power (.power x (-2)) (-3)) ∧
    (mkPower o me (.sum 0 [(2, x), (2, y)]) (-1)).bind (fun r => mkProduct o me [.number 0, r]) =
      .value (.product 0 [.power (.sum 0 [(1, x), (1, y)]) (-1)])

/-! ## Strict evaluation of numbers (TRM-R07) -/

/-- Strict evaluation, positive (TRM-R07): `0⁰ = 1`. -/
def ZeroToTheZeroIsOne : Prop :=
  mkPower Orders.sample defaultMaxExponent (.number 0) 0 = .value (.number 1)

/-- Strict evaluation, negative (TRM-R07): `0 (1/0)`, `(1/0)⁰`, `0⁻¹` and
`x / (0 x⁻¹)` fail with `DivisionByZero`, since `1/0` fails as it is built;
and under the default limits `x / x^(2³²)` fails with `ResourceLimit` naming
`max_exponent`, as `x^(2³²)` is built. -/
def StrictEvaluationFailures : Prop :=
  let o := Orders.sample
  let me := defaultMaxExponent
  let x : Term := .symbol "x"
  (mkDivide o me (.number 1) (.number 0)).bind (fun q => mkProduct o me [.number 0, q]) =
      .fault .divisionByZero ∧
    (mkDivide o me (.number 1) (.number 0)).bind (fun q => mkPower o me q 0) =
      .fault .divisionByZero ∧
    mkPower o me (.number 0) (-1) = .fault .divisionByZero ∧
    mkDivide o me x (.product 0 [.power x (-1)]) = .fault .divisionByZero ∧
    (mkPower o me x (2 ^ 32)).bind (fun p => mkDivide o me x p) = .resourceLimit .exponent

/-! ## Accounting under the request context (TRM-R08) -/

/-- Logical bytes, positive (TRM-R08): for a coefficient `c ≠ 1` and `k ≥ 2`,
the product `c x^k` costs `rb(c) + ℓ + |k| + 12` bytes, where `rb(c)` is the
bytes of the rational, `ℓ` those of the name and `|k|` the bit length of `k`;
and `x y` costs `ℓx + ℓy + 4`. The bytes of constants, calls and conditions
are any parameters. -/
def LogicalBytesOfProducts : Prop :=
  (∀ (p : ByteParams) (c : ℚ) (name : String) (k : ℤ), c ≠ 1 → 2 ≤ k →
    Term.bytes p (.product c [.power (.symbol name) k]) =
      ratBytes c + name.utf8ByteSize + k.natAbs.size + 12) ∧
  ∀ (p : ByteParams) (a b : String),
    Term.bytes p (.product 1 [.symbol a, .symbol b]) = a.utf8ByteSize + b.utf8ByteSize + 4

/-- Tree size, negative (TRM-R08): a subterm counts once for each
occurrence, so `(x + y)² (x + y)⁻¹` has the size 9, not 6. -/
def SharedSubtermsCountOncePerOccurrence : Prop :=
  let o := Orders.sample
  let me := defaultMaxExponent
  let s : Term := .sum 0 [(1, .symbol "x"), (1, .symbol "y")]
  let t : Term := .product 1 [.power s 2, .power s (-1)]
  (do
      let p ← mkPower o me s 2
      let r ← mkPower o me s (-1)
      mkProduct o me [p, r] : Result Term) = .value t ∧
    t.size = 9

/-! ## Depth and drop (TRM-R09) -/

/-- Depth, positive (TRM-R09): a number and a symbol have the depth 1, and
`x y` has the depth 2. -/
def DepthOfLeavesAndProducts : Prop :=
  (∀ q : ℚ, (Term.number q).depth = 1) ∧ (∀ name : String, (Term.symbol name).depth = 1) ∧
    (mkProduct Orders.sample defaultMaxExponent [.symbol "x", .symbol "y"]).map Term.depth =
      .value 2

/-- Depth, negative (TRM-R09): `x + y + z` has the depth 2, not its size 4. -/
def DepthIsNotSize : Prop :=
  (mkSum Orders.sample [.symbol "x", .symbol "y", .symbol "z"]).map
      (fun t => (t.depth, t.size)) = .value (2, 4)

/-! ## Deterministic display (TRM-R10) -/

/-- Display, positive (TRM-R10): `2 (x + y)`, `(x + y) + (x + y)` and
`(2 x + y) + y` are all written `2*x + 2*y`, whatever the texts of algebraic
constants and conditions. -/
def DisplayIsTheSameForEveryConstruction : Prop :=
  let o := Orders.sample
  let me := defaultMaxExponent
  let x : Term := .symbol "x"
  let y : Term := .symbol "y"
  let s : Term := .sum 0 [(1, x), (1, y)]
  ∀ p : DisplayParams,
    (mkProduct o me [.number 2, s]).map (Term.display p) = .value "2*x + 2*y" ∧
      (mkSum o [s, s]).map (Term.display p) = .value "2*x + 2*y" ∧
      (mkSum o [.sum 0 [(2, x), (1, y)], y]).map (Term.display p) = .value "2*x + 2*y"

/-- Display, negative (TRM-R10): `(1 - x)⁻¹` is written `-(-1 + x)^(-1)`,
from its canonical form `-(x - 1)⁻¹`, not `(1 - x)^(-1)`. -/
def DisplayOfANegatedReciprocal : Prop :=
  let o := Orders.sample
  let me := defaultMaxExponent
  ∀ p : DisplayParams,
    ((mkSubtract o me (.number 1) (.symbol "x")).bind fun d => mkPower o me d (-1)).map
      (Term.display p) = .value "-(-1 + x)^(-1)"

/-! ## Symbols and reserved names (TRM-R11) -/

/-- Symbol names, positive (TRM-R11): `x_1`, `Pi`, `ii` and `pi2` are
symbols. -/
def SymbolNames : Prop :=
  mkSymbol "x_1" = .value (.symbol "x_1") ∧ mkSymbol "Pi" = .value (.symbol "Pi") ∧
    mkSymbol "ii" = .value (.symbol "ii") ∧ mkSymbol "pi2" = .value (.symbol "pi2")

/-- Symbol names, negative (TRM-R11): `pi`, `i` and `undefined` fail with
`Unsupported` and the span of the name; `2x` fails with `Syntax` and the span
of the digit, and the empty name with the empty span at 0. -/
def ReservedAndMalformedNames : Prop :=
  mkSymbol "pi" = .fault (.unsupported (some ⟨0, 2⟩)) ∧
    mkSymbol "i" = .fault (.unsupported (some ⟨0, 1⟩)) ∧
    mkSymbol "undefined" = .fault (.unsupported (some ⟨0, 9⟩)) ∧
    mkSymbol "2x" = .fault (.syntax (some ⟨0, 1⟩)) ∧
    mkSymbol "" = .fault (.syntax (some ⟨0, 0⟩))

/-! ## Evaluation reads the canonical term (TRM-R12) -/

/-- `eval`, positive (TRM-R12): `eval` of `1/3 + 1/6` is `1/2`, and of `i i`
is `-1`, whatever the answer for closed formal nodes. -/
def EvalGivesTheCanonicalTerm : Prop :=
  let o := Orders.sample
  let me := defaultMaxExponent
  ∀ cf : ClosedFormal,
    (mkSum o [.number (1 / 3), .number (1 / 6)]).bind (Term.eval cf) =
        .value (.value (.number (1 / 2))) ∧
      (mkProduct o me [Term.imaginaryUnit, Term.imaginaryUnit]).bind (Term.eval cf) =
        .value (.value (.number (-1)))

/-- `eval`, negative (TRM-R12): `eval` of `x / x` and of `0 x⁻¹` fails with
`UnknownSymbol`, since their canonical terms hold `x`. -/
def EvalOfFreeSymbolsFails : Prop :=
  let o := Orders.sample
  let me := defaultMaxExponent
  let x : Term := .symbol "x"
  ∀ cf : ClosedFormal,
    (mkDivide o me x x).bind (Term.eval cf) = .fault .unknownSymbol ∧
      ((mkPower o me x (-1)).bind fun r => mkProduct o me [.number 0, r]).bind (Term.eval cf) =
        .fault .unknownSymbol

/-! ## Constants (TRM-R13) -/

/-- Constants, positive (TRM-R13): `i i = -1`, `i⁻³ = i` and `π π⁻¹ = 1`; and
a constant comes between the numbers and the symbols, so `x + π + 2` is
`2 + π + x`. -/
def ConstantsMergeAndOrder : Prop :=
  let o := Orders.sample
  let me := defaultMaxExponent
  let i : Term := .constant (.named .i)
  let pi : Term := .constant (.named .pi)
  let x : Term := .symbol "x"
  mkProduct o me [i, i] = .value (.number (-1)) ∧ mkPower o me i (-3) = .value i ∧
    (mkPower o me pi (-1)).bind (fun r => mkProduct o me [pi, r]) = .value (.number 1) ∧
    mkSum o [x, pi, .number 2] = .value (.sum 2 [(1, pi), (1, x)])

/-- Constants, negative (TRM-R13): a constant is never in `N`, so `π⁻¹` has
no negative power in that sense; the algebraic constant of the real root of
`x³ - x - 1`, which no closed form covers, is not folded, so its cube stays
a power; and the hand-written power `i²` is not canonical. -/
def ConstantsAreNotNegativeBases : Prop :=
  let o := Orders.sample
  let me := defaultMaxExponent
  let pi : Term := .constant (.named .pi)
  let c : Constant := .real ⟨[-1, -1, 0, 1], 0⟩
  (mkPower o me pi (-1)).map Term.negBases = .value [] ∧
    (mkPower o me pi (-1)).map Term.hasNegativePower = .value false ∧
    c.hasClosedForm = false ∧
    mkPower o me (.constant c) 3 = .value (.power (.constant c) 3) ∧
    ¬Term.Canonical o me RegistryRules.empty (.power Term.imaginaryUnit 2)

/-! ## Calls (TRM-R14) -/

/-- Calls, positive (TRM-R14), built under the rules that keep every call:
calls are atoms that merge by structure, `sin(x + y) sin(y + x) = sin(x + y)²`
and `exp(x + y) - exp(y + x) = 0`; and for `s = √x`, `s s s s` and
`(s s) (s s)` are both `x²`, by the rule of the powers of roots. -/
def CallsMergeAsAtoms : Prop :=
  let o := Orders.sample
  let me := defaultMaxExponent
  let call := fun (name : String) (args : List Term) =>
    mkCall me RegistryRules.empty ⟨name, .registered⟩ args
  let x : Term := .symbol "x"
  let y : Term := .symbol "y"
  let s : Term := .sum 0 [(1, x), (1, y)]
  (do
      let u ← mkSum o [x, y]
      let v ← mkSum o [y, x]
      let a ← call "sin" [u]
      let b ← call "sin" [v]
      mkProduct o me [a, b] : Result Term) =
      .value (.power (.call ⟨"sin", .registered⟩ [s]) 2) ∧
    (do
      let u ← mkSum o [x, y]
      let v ← mkSum o [y, x]
      let a ← call "exp" [u]
      let b ← call "exp" [v]
      mkSubtract o me a b : Result Term) = .value (.number 0) ∧
    (call "sqrt" [x]).bind (fun r => mkProduct o me [r, r, r, r]) = .value (.power x 2) ∧
    (do
      let r ← call "sqrt" [x]
      let rr ← mkProduct o me [r, r]
      mkProduct o me [rr, rr] : Result Term) = .value (.power x 2)

/-- Calls, negative (TRM-R14), built under the rules that keep every call: the
arguments of a call are not sorted, so `f(x, y)` and `f(y, x)` differ; a call
is not expanded, so `sin(x) (sin(x) + 1)` is not distributed; and the rule
of the powers of roots leaves negative exponents, so `(√x)⁻²` stays. -/
def CallsAreNotExpanded : Prop :=
  let o := Orders.sample
  let me := defaultMaxExponent
  let call := fun (name : String) (args : List Term) =>
    mkCall me RegistryRules.empty ⟨name, .registered⟩ args
  let x : Term := .symbol "x"
  let y : Term := .symbol "y"
  let sinx : Term := .call ⟨"sin", .registered⟩ [x]
  call "f" [x, y] = .value (.call ⟨"f", .registered⟩ [x, y]) ∧
    call "f" [x, y] ≠ call "f" [y, x] ∧
    (do
      let a ← call "sin" [x]
      let b ← mkSum o [a, .number 1]
      mkProduct o me [a, b] : Result Term) = .value (.product 1 [sinx, .sum 1 [(1, sinx)]]) ∧
    (call "sqrt" [x]).bind (fun r => mkPower o me r (-2)) =
      .value (.power (.call ⟨"sqrt", .registered⟩ [x]) (-2))

/-! ## Conditions (TRM-R15) -/

/-- Conditions, positive (TRM-R15): a condition has the rank 7 and comes after
the sums; and `piecewise(true, a, b)` is `a` and `piecewise(false, a, b)` is
`b`. -/
def ConditionsRankLastAndSelectBranches : Prop :=
  let o := Orders.sample
  let me := defaultMaxExponent
  let x : Term := .symbol "x"
  let y : Term := .symbol "y"
  (Term.ofBool true).rank = 7 ∧
    Term.cmp o (.sum 0 [(1, x), (1, y)]) (Term.ofBool true) = .lt ∧
    mkCall me RegistryRules.empty Head.piecewise [Term.ofBool true, x, y] = .value x ∧
    mkCall me RegistryRules.empty Head.piecewise [Term.ofBool false, x, y] = .value y

/-- Conditions, negative (TRM-R15): an operand of the wrong class fails with
`Syntax`: a condition as an operand of a sum, a number as the condition of
`piecewise`, and a value as the operand of `not`. -/
def ConditionsInValuePositionsFail : Prop :=
  let o := Orders.sample
  let me := defaultMaxExponent
  let x : Term := .symbol "x"
  let y : Term := .symbol "y"
  mkSum o [x, Term.ofBool true] = .fault (.syntax none) ∧
    mkCall me RegistryRules.empty Head.piecewise [.number 1, x, y] = .fault (.syntax none) ∧
    mkCondition .not [x] = .fault (.syntax none)

end Kalyx.Statements.Terms

end
