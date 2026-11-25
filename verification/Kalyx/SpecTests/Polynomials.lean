module

public meta import Kalyx.Spec.Polynomials.Division
public meta import Kalyx.Spec.Polynomials.Evaluate
public meta import Kalyx.Spec.Polynomials.Maps
public meta import Kalyx.Spec.Polynomials.Terms

/-!
# Replays of the vectors of the polynomials

The vectors whose answers the polynomials decide, replayed through the
specification of `Kalyx.Spec.Polynomials` with `#guard`: the rows of
`vectors/r02.tsv` whose operation is `expand` or `diff`, the rows of
`vectors/cli_cases.tsv` of `expand`, `diff`, `divrem`, `gcd` and `gcdex`, and
the rows of `vectors/library.tsv` of `expand`; then the examples of the
requirements, the computations of the statements of
`Kalyx.Statements.Polynomials` that a `#guard` can run.

Each input is written as an input tree `E`, unnormalized, and `E.canonAt`
builds its canonical term through the constructors of the term core, an
operator at a time, as a parse builds it; the answer is read back the same
way. `expand` and `diff` run as the operations of a request with the variable
of the row (`expandOperation`, `diffOperation`), and their results are
compared with the canonical term of the answer by structure, as the vectors
compare them; an error is compared by its kind, and `ResourceLimit` by its
field as well. The parser is not part of the replay: an input tree is written
in Lean, whose operators have the precedence of kalyx's grammar, and the
answers of `vectors/library.tsv`, which are written in the display of the
earlier implementation, are read as the same terms.

The operations `divrem`, `gcd` and `gcdex` belong to the command surface,
which is not part of this specification: their rows are replayed by the
shared algorithms over `ℚ`, on the polynomials of their operands, each
expanded in the ring of the variable, with the quotient, the remainder, the
GCD and the cofactors converted back to terms by the same ring.

The longest answers of `vectors/r02.tsv`, the dense powers and products, are
written by generators from their formulas: the binomial coefficients of
`(x/2 + 1/3)ⁿ` and of the derivative of `(x + 1)ⁿ`, and the coefficients
`1, 2, …, n + 1, …, 2, 1` of `(1 + x + … + xⁿ)²`. The inputs are generated
the same way. The two longest are compared by the coefficients of the
polynomial as well.
-/

namespace Kalyx.SpecTests.Polynomials

open Kalyx.Spec.Fields Kalyx.Spec.Polynomials
open Kalyx.Spec.Terms (Term Orders mkSymbol mkSum mkSubtract mkProduct mkDivide mkNegate mkPower
  defaultMaxExponent)

/-! ## Input trees -/

/-- An input tree, as the input text writes a term: numbers, symbols, the
operators and integer powers. -/
inductive E where
  | num (q : ℚ)
  | sym (name : String)
  | add (a b : E)
  | sub (a b : E)
  | mul (a b : E)
  | div (a b : E)
  | neg (a : E)
  | pow (a : E) (k : ℤ)

meta instance (n : ℕ) : OfNat E n := ⟨.num n⟩
meta instance : Add E := ⟨.add⟩
meta instance : Sub E := ⟨.sub⟩
meta instance : Mul E := ⟨.mul⟩
meta instance : Div E := ⟨.div⟩
meta instance : Neg E := ⟨.neg⟩
meta instance : HPow E ℕ E := ⟨fun a k => .pow a k⟩
meta instance : HPow E ℤ E := ⟨fun a k => .pow a k⟩

/-- The symbol `x`. -/
meta def x : E := .sym "x"

/-- The symbol `y`. -/
meta def y : E := .sym "y"

/-- The symbol `t`. -/
meta def t : E := .sym "t"

/-- A rational number. -/
meta def q (r : ℚ) : E := .num r

/-- The canonical term of an input tree under `maxExponent`, built through the
constructors of the term core under the order `Orders.sample`. The first error
in the order of the input is the result. -/
meta def E.canonAt (maxExponent : ℕ) : E → Kalyx.Spec.Terms.Result Term
  | .num r => .value (.number r)
  | .sym name => mkSymbol name
  | .add a b => do mkSum Orders.sample [← a.canonAt maxExponent, ← b.canonAt maxExponent]
  | .sub a b => do
    mkSubtract Orders.sample maxExponent (← a.canonAt maxExponent) (← b.canonAt maxExponent)
  | .mul a b => do
    mkProduct Orders.sample maxExponent [← a.canonAt maxExponent, ← b.canonAt maxExponent]
  | .div a b => do
    mkDivide Orders.sample maxExponent (← a.canonAt maxExponent) (← b.canonAt maxExponent)
  | .neg a => do mkNegate Orders.sample maxExponent (← a.canonAt maxExponent)
  | .pow a k => do mkPower Orders.sample maxExponent (← a.canonAt maxExponent) k

/-- The canonical term of an input tree under the default limit, none when it
fails. -/
meta def E.term (e : E) : Option Term :=
  match e.canonAt defaultMaxExponent with
  | .value u => some u
  | _ => none

/-- The ring `ℚ[x]` of the variable `name`. -/
meta def ring (name : String) : PolynomialRing Rationals := ⟨⟨⟩, name⟩

/-- The result of `expand` of a request with the variable `name` on the input,
none when the input builds no term. -/
meta def expandOf (name : String) (input : E) (L : Limits := Limits.default) :
    Option (PolyResult Term) :=
  input.term.map (expandOperation Orders.sample L name)

/-- The result of `diff` of a request with the variable `name` on the input,
none when the input builds no term. -/
meta def diffOf (name : String) (input : E) (L : Limits := Limits.default) :
    Option (PolyResult Term) :=
  input.term.map (diffOperation Orders.sample L name)

/-- `expand` of the input gives the canonical term of the answer. -/
meta def expands (name : String) (input answer : E) : Bool :=
  match answer.term with
  | some u => expandOf name input == some (.value u)
  | none => false

/-- `diff` of the input gives the canonical term of the answer. -/
meta def diffs (name : String) (input answer : E) : Bool :=
  match answer.term with
  | some u => diffOf name input == some (.value u)
  | none => false

/-- The polynomial of an input in the ring of the variable `name`. -/
meta def polyOf (name : String) (input : E) : PolyResult (Poly Fraction) :=
  match input.term with
  | some u => (ring name).expand Limits.default u
  | none => .fault (.term .internal)

/-- The term of a polynomial converted back by the ring of the variable
`name`. -/
meta def termOf (name : String) (a : Poly Fraction) : PolyResult Term :=
  (ring name).toTerm Orders.sample Limits.default a

/-- The canonical term of an answer as a result. -/
meta def answerOf (answer : E) : PolyResult Term :=
  match answer.term with
  | some u => .value u
  | none => .fault (.term .internal)

/-- `divrem` of two inputs in the variable `name`: the quotient and the
remainder of their polynomials, converted back to terms. -/
meta def divremOf (name : String) (a b : E) : PolyResult (Term × Term) := do
  let (q, r) ← Poly.divRem Rationals.field ⟨⟩ (← polyOf name a) (← polyOf name b)
  pure (← termOf name q, ← termOf name r)

/-- `gcd` of two inputs in the variable `name`, converted back to a term. -/
meta def gcdOf (name : String) (a b : E) : PolyResult Term := do
  termOf name (← Poly.monicGcd Rationals.field ⟨⟩ (← polyOf name a) (← polyOf name b))

/-- `gcdex` of two inputs in the variable `name`: the left and the right
cofactors and the GCD, converted back to terms. -/
meta def gcdexOf (name : String) (a b : E) : PolyResult (Term × Term × Term) := do
  let e ← Poly.extendedGcd Rationals.field ⟨⟩ (← polyOf name a) (← polyOf name b)
  pure (← termOf name e.left, ← termOf name e.right, ← termOf name e.gcd)

/-- The polynomial over `ℚ` with the terms `(d, c)` of `l`. -/
meta def mk (l : List (ℕ × ℚ)) : Poly Fraction := ⟨l.map fun (d, c) => (d, Fraction.ofRat c)⟩

/-! ## Generators -/

/-- The term `c xᵏ` of an answer. -/
meta def monomial : ℕ × ℚ → E
  | (0, c) => q c
  | (1, c) => q c * x
  | (k, c) => q c * x ^ k

/-- The sum of the terms `c xᵏ` of a list, added from the left. -/
meta def sumOf (terms : List (ℕ × ℚ)) : E :=
  match terms.map monomial with
  | [] => 0
  | a :: rest => rest.foldl .add a

/-- The coefficients of `(x/2 + 1/3)ⁿ`, from the highest degree. -/
meta def denseRational (n : ℕ) : List (ℕ × ℚ) :=
  (List.range (n + 1)).reverse.map fun k => (k, (n.choose k : ℚ) * (1 / 2) ^ k * (1 / 3) ^ (n - k))

/-- The coefficients of the derivative of `(x + 1)ⁿ`, from the highest
degree. -/
meta def derivativeOfBinomial (n : ℕ) : List (ℕ × ℚ) :=
  (List.range n).reverse.map fun k => (k, ((k + 1) * n.choose (k + 1) : ℕ))

/-- `1 + x + … + xⁿ`, added from the left. -/
meta def geometric (n : ℕ) : E := sumOf ((List.range (n + 1)).map fun k => (k, 1))

/-- The coefficients of `(1 + x + … + xⁿ)²`, from the highest degree. -/
meta def squareOfGeometric (n : ℕ) : List (ℕ × ℚ) :=
  (List.range (2 * n + 1)).reverse.map fun k => (k, ((min k (2 * n - k) + 1 : ℕ) : ℚ))

/-! ## `vectors/r02.tsv` -/

-- binomial (expand): `(x+1)^5` is `x^5 + 5*x^4 + 10*x^3 + 10*x^2 + 5*x + 1`
#guard expands "x" ((x + 1) ^ 5) (x ^ 5 + 5 * x ^ 4 + 10 * x ^ 3 + 10 * x ^ 2 + 5 * x + 1)

-- factor_product (expand): `(x-1)*(x+1)*(x^2+1)` is `x^4 - 1`
#guard expands "x" ((x - 1) * (x + 1) * (x ^ 2 + 1)) (x ^ 4 - 1)

-- rational_coefficients (expand): `(x/2 + 1/3)^3` is `1/8*x^3 + 1/4*x^2 + 1/6*x + 1/27`
#guard expands "x" ((x / 2 + 1 / 3) ^ 3) (1 / 8 * x ^ 3 + 1 / 4 * x ^ 2 + 1 / 6 * x + 1 / 27)

-- derivative (diff): `(x+1)^5` is `5*x^4 + 20*x^3 + 30*x^2 + 20*x + 5`
#guard diffs "x" ((x + 1) ^ 5) (5 * x ^ 4 + 20 * x ^ 3 + 30 * x ^ 2 + 20 * x + 5)

-- named_variable (diff, variable `t`): `(t^3-2*t)/3` is `t^2 - 2/3`
#guard diffs "t" ((t ^ 3 - 2 * t) / 3) (t ^ 2 - 2 / 3)

-- cancellation (expand): `(x+1)^2-x^2-2*x-1` is `0`
#guard expands "x" ((x + 1) ^ 2 - x ^ 2 - 2 * x - 1) 0

-- dense_rational_8 (expand): `(x/2+1/3)^8` is `1/256*x^8 + 1/48*x^7 + 7/144*x^6 + ...`
#guard expands "x" ((x / 2 + 1 / 3) ^ 8) (sumOf (denseRational 8))

-- derivative_8 (diff): `(x+1)^8` is `8*x^7 + 56*x^6 + 168*x^5 + 280*x^4 + ...`
#guard diffs "x" ((x + 1) ^ 8) (sumOf (derivativeOfBinomial 8))

-- coefficient_cancellation_8 (expand): `(x+1)^8-(x+1)^8` is `0`
#guard expands "x" ((x + 1) ^ 8 - (x + 1) ^ 8) 0

-- dense_rational_32 (expand): `(x/2+1/3)^32` is `1/4294967296*x^32 + 1/201326592*x^31 + ...`
#guard expands "x" ((x / 2 + 1 / 3) ^ 32) (sumOf (denseRational 32))

-- derivative_32 (diff): `(x+1)^32` is `32*x^31 + 992*x^30 + 14880*x^29 + ...`
#guard diffs "x" ((x + 1) ^ 32) (sumOf (derivativeOfBinomial 32))

-- coefficient_cancellation_32 (expand): `(x+1)^32-(x+1)^32` is `0`
#guard expands "x" ((x + 1) ^ 32 - (x + 1) ^ 32) 0

-- dense_rational_64 (expand): `(x/2+1/3)^64` is `1/18446744073709551616*x^64 + ...`
#guard expands "x" ((x / 2 + 1 / 3) ^ 64) (sumOf (denseRational 64))

-- derivative_64 (diff): `(x+1)^64` is `64*x^63 + 4032*x^62 + 124992*x^61 + ...`
#guard diffs "x" ((x + 1) ^ 64) (sumOf (derivativeOfBinomial 64))

-- coefficient_cancellation_64 (expand): `(x+1)^64-(x+1)^64` is `0`
#guard expands "x" ((x + 1) ^ 64 - (x + 1) ^ 64) 0

-- dense_rational_128 (expand): `(x/2+1/3)^128` is `1/3402823669209384634633746074...`
#guard expands "x" ((x / 2 + 1 / 3) ^ 128) (sumOf (denseRational 128))
#guard polyOf "x" ((x / 2 + 1 / 3) ^ 128) == .value (mk (denseRational 128).reverse)

-- derivative_128 (diff): `(x+1)^128` is `128*x^127 + 16256*x^126 + 1024128*x^125 + ...`
#guard diffs "x" ((x + 1) ^ 128) (sumOf (derivativeOfBinomial 128))
#guard (polyOf "x" ((x + 1) ^ 128)).bind ((ring "x").derivative rationalRing Limits.default) ==
  .value (mk (derivativeOfBinomial 128).reverse)

-- coefficient_cancellation_128 (expand): `(x+1)^128-(x+1)^128` is `0`
#guard expands "x" ((x + 1) ^ 128 - (x + 1) ^ 128) 0

-- dense_product_8 (expand): `(1+x+x^2+...+x^8)*(1+x+...+x^8)` is `x^16 + 2*x^15 + ...`
#guard expands "x" (geometric 8 * geometric 8) (sumOf (squareOfGeometric 8))

-- dense_product_32 (expand): `(1+x+x^2+...+x^32)*(1+x+...+x^32)` is `x^64 + 2*x^63 + ...`
#guard expands "x" (geometric 32 * geometric 32) (sumOf (squareOfGeometric 32))

-- dense_product_64 (expand): `(1+x+x^2+...+x^64)*(1+x+...+x^64)` is `x^128 + 2*x^127 + ...`
#guard expands "x" (geometric 64 * geometric 64) (sumOf (squareOfGeometric 64))

-- sparse_product_8 (expand): `(x^8+1)*(x^8-1)` is `x^16 - 1`
#guard expands "x" ((x ^ 8 + 1) * (x ^ 8 - 1)) (x ^ 16 - 1)

-- sparse_product_32 (expand): `(x^32+1)*(x^32-1)` is `x^64 - 1`
#guard expands "x" ((x ^ 32 + 1) * (x ^ 32 - 1)) (x ^ 64 - 1)

-- sparse_product_128 (expand): `(x^128+1)*(x^128-1)` is `x^256 - 1`
#guard expands "x" ((x ^ 128 + 1) * (x ^ 128 - 1)) (x ^ 256 - 1)

-- unknown_symbol_1 (expand): `x+y` fails with `UnknownSymbol`
#guard expandOf "x" (x + y) == some (.fault (.term .unknownSymbol))

-- rational_function_1 (expand): `(x^2-1)/(x-1)` fails with `NotPolynomial`
#guard expandOf "x" ((x ^ 2 - 1) / (x - 1)) == some (.fault .notPolynomial)

-- degree_limit_1 (expand, `max_exponent=256`): `x^257` fails with `ResourceLimit`
-- naming `max_exponent`, when the term core builds it under the limit and when
-- the expansion takes it under the limit
#guard E.canonAt 256 (x ^ 257) == .resourceLimit .exponent
#guard expandOf "x" (x ^ 257) { Limits.default with maxExponent := 256 } ==
  some (.resourceLimit .exponent)

/-! ## `vectors/cli_cases.tsv` -/

-- algebra/diff-rejects-invalid-variable (diff, `--var !`): `x` fails with `Syntax`
#guard diffOf "!" x == some (.fault (.term (.syntax none)))

-- algebra/diff-with-named-variable (diff, `--var t`): `t^3/3` is `t^2`
#guard diffs "t" (t ^ 3 / 3) (t ^ 2)

-- algebra/divrem-exact-division (divrem): `x^3+1`, `x+1` is the quotient `x^2 - x + 1`
-- and the remainder `0`
#guard divremOf "x" (x ^ 3 + 1) (x + 1) == (do pure (← answerOf (x ^ 2 - x + 1), ← answerOf 0))

-- algebra/divrem-rejects-zero-divisor (divrem): `1`, `0` fails with `DivisionByZero`
#guard divremOf "x" 1 0 == .fault (.field .divisionByZero)

-- algebra/divrem-with-remainder-and-named-variable (divrem, `--var t`): `t^2`, `t+1` is
-- the quotient `t - 1` and the remainder `1`
#guard divremOf "t" (t ^ 2) (t + 1) == (do pure (← answerOf (t - 1), ← answerOf 1))

-- algebra/expand-binomial-cube (expand): `(x+1)^3` is `x^3 + 3*x^2 + 3*x + 1`
#guard expands "x" ((x + 1) ^ 3) (x ^ 3 + 3 * x ^ 2 + 3 * x + 1)

-- algebra/expand-rejects-foreign-symbol (expand): `x/y` fails with `UnknownSymbol`
#guard expandOf "x" (x / y) == some (.fault (.term .unknownSymbol))

-- algebra/expand-rejects-polynomial-division (expand): `x/x` fails with `NotPolynomial`
#guard expandOf "x" (x / x) == some (.fault .notPolynomial)

-- algebra/gcd-is-monic-common-factor (gcd): `x^2-1`, `x^2-2*x+1` is `x - 1`
#guard gcdOf "x" (x ^ 2 - 1) (x ^ 2 - 2 * x + 1) == answerOf (x - 1)

-- algebra/gcd-of-zeros-is-zero (gcd): `0`, `0` is `0`
#guard gcdOf "x" 0 0 == answerOf 0

-- algebra/gcd-rejects-foreign-symbol (gcd): `x`, `y` fails with `UnknownSymbol`, in
-- either order of the operands
#guard gcdOf "x" x y == .fault (.term .unknownSymbol)
#guard gcdOf "x" y x == .fault (.term .unknownSymbol)

-- algebra/gcdex-reports-bezout-coefficients (gcdex): `x^2-1`, `x-1` is the left
-- cofactor `0`, the right cofactor `1` and the GCD `x - 1`
#guard gcdexOf "x" (x ^ 2 - 1) (x - 1) ==
  (do pure (← answerOf 0, ← answerOf 1, ← answerOf (x - 1)))

/-! ## `vectors/library.tsv` -/

-- i04_none_expand_w1000000 (expand): `(-x)^2` is `(x)^(2)`
#guard expands "x" ((-x) ^ 2) (x ^ 2)

-- i08_none_expand_w1000000 (expand): `(x+x)^3` is `(8*(x)^(3))`
#guard expands "x" ((x + x) ^ 3) (8 * x ^ 3)

-- i09_none_expand_w1000000 (expand): `-x` is `(-1*x)`
#guard expands "x" (-x) (-1 * x)

-- i10_none_expand_w1000000 (expand): `-x^3` is `(-1*(x)^(3))`
#guard expands "x" (-x ^ 3) (-1 * x ^ 3)

-- i11_none_expand_w1000000 (expand): `0` is `0`
#guard expands "x" 0 0

-- i13_none_expand_w1000000 (expand): `0^0` is `1`
#guard expands "x" (0 ^ 0) 1

-- i90_none_expand_w1000000 (expand): `x` is `x`
#guard expands "x" x x

-- i91_none_expand_w1000000 (expand): `x+x-x` is `x`
#guard expands "x" (x + x - x) x

/-! ## The examples of the requirements

The computations of the examples of `Kalyx.Statements.Polynomials`, each
named in a comment, with the same parameters; the negative example of
canonical forms is a proposition about lists, not a computation. -/

/-- The polynomial over a prime field with the residues `(d, c)` of `l`. -/
meta def pr (l : List (ℕ × ℕ)) : Poly PrimeResidue := ⟨l.map fun (d, c) => (d, ⟨c⟩)⟩

/-- `f` holds of the prime field that the constructor builds from `p`. -/
meta def withPrime (p : ℕ) (f : PrimeField → Bool) : Bool :=
  match PrimeField.new p with
  | .built F => f F
  | .rejected => false

/-- The methods of the prime fields as a coefficient ring. -/
meta def primeRing : CoefficientRing PrimeField PrimeResidue Empty :=
  PrimeField.field.toCoefficientRing

/-- The default limits with `max_exponent` set to `n`. -/
meta def withExponent (n : ℕ) : Limits := { Limits.default with maxExponent := n }

/-- The default limits with `max_nodes` set to `n`. -/
meta def withNodes (n : ℕ) : Limits := { Limits.default with maxNodes := n }

/-- The default limits with `max_depth` set to `n`. -/
meta def withDepth (n : ℕ) : Limits := { Limits.default with maxDepth := n }

/-- `x + 1`, the polynomial of most examples. -/
meta def x1 : Poly Fraction := mk [(0, 1), (1, 1)]

-- SumsKeepOneTermOrNone
#guard (ring "x").add rationalRing Limits.default x1 (mk [(0, -1), (1, 1)]) == .value (mk [(1, 2)])
#guard (do
  let r := ring "x"
  let s ← r.power rationalRing Limits.default x1 2
  let s ← r.subtract rationalRing Limits.default s (mk [(2, 1)])
  let s ← r.subtract rationalRing Limits.default s (mk [(1, 2)])
  r.subtract rationalRing Limits.default s (mk [(0, 1)])) == .value Poly.zero

-- PowersOfZeroAndOfABinomial, PowersCheckTheExponentFirst, PowersAgreeUnderWiderLimits,
-- ExceededLimitsNameTheirField
#guard (ring "x").power rationalRing Limits.default Poly.zero 0 == .value (mk [(0, 1)])
#guard [2, 100, 4096].all fun n =>
  (ring "x").power rationalRing (withExponent n) x1 2 == .value (mk [(0, 1), (1, 2), (2, 1)])
#guard (ring "x").power rationalRing (withExponent 1) (mk [(0, 2)]) 2 == .resourceLimit .exponent
#guard (ring "x").power rationalRing (withExponent 150) (mk [(0, 1), (100, 1)]) 2 ==
  .resourceLimit .exponent
#guard (ring "x").power rationalRing (withExponent 1) x1 2 == .resourceLimit .exponent

-- BinomialCoefficientsVanishModuloSeven, ZeroDivisorsLeaveNoTerm
#guard withPrime 7 fun F =>
  (⟨F, "x"⟩ : PolynomialRing PrimeField).power primeRing Limits.default (pr [(0, 1), (1, 1)]) 7 ==
    .value (pr [(0, 1), (7, 1)])
#guard (⟨⟨6⟩, "x"⟩ : PolynomialRing ResidueRing).multiply
  (ResidueRing.ring fun _ a => ⟨1, a.size + 4⟩).toCoefficientRing Limits.default
  ⟨[(1, 2)]⟩ ⟨[(1, 3)]⟩ == .value Poly.zero

-- RingOfAVariableName, ReservedAndMalformedVariables
#guard PolynomialRing.new (⟨⟩ : Rationals) "t_1" == .value (ring "t_1")
#guard PolynomialRing.new (⟨⟩ : Rationals) "pi" == .fault (.term (.unsupported (some ⟨0, 2⟩)))
#guard PolynomialRing.new (⟨⟩ : Rationals) "" == .fault (.term (.syntax (some ⟨0, 0⟩)))
#guard PolynomialRing.new (⟨⟩ : Rationals) "1x" == .fault (.term (.syntax (some ⟨0, 1⟩)))

-- DerivativeByANamedVariable, TheVariableIsCheckedBeforeTheInput
#guard diffs "t" (q (1 / 3) * t ^ 3) (t ^ 2)
#guard diffOf "!" y == some (.fault (.term (.syntax none)))
#guard expandOf "!" y == some (.fault (.term (.syntax none)))
#guard expandOf "X" x == some (.fault (.term .unknownSymbol))

-- StorageOfASparsePolynomial, NodesBoundTermsAndPartialSums
#guard (ring "x").storage rationalRing (mk [(0, -1), (256, 1)]) == ⟨7, 36⟩
#guard (ring "x").check rationalRing (withNodes 40) (mk ((List.range 10).map fun d => (d, 1))) ==
  .resourceLimit .nodes
#guard (ring "x").multiply rationalRing (withNodes 28) (mk [(0, 1), (1, 1), (2, 1)])
  (mk [(0, 1), (2, -1), (4, 1)]) == .resourceLimit .nodes
#guard
  let product := mk [(0, 1), (1, 1), (3, -1), (5, 1), (6, 1)]
  (ring "x").check rationalRing (withNodes 28) product == .value product

-- TermsExpandIntoPolynomials, ForeignSymbolsAndNegativePowersFail
#guard polyOf "x" ((x + 1) ^ 2 - x ^ 2 - 2 * x - 1) == .value Poly.zero
#guard polyOf "x" ((x / 2 + 1 / 3) ^ 3) ==
  .value (mk [(0, 1 / 27), (1, 1 / 6), (2, 1 / 4), (3, 1 / 8)])
#guard polyOf "x" (y ^ (-1 : ℤ)) == .fault (.term .unknownSymbol)
#guard polyOf "x" (x * x ^ (-1 : ℤ)) == .fault .notPolynomial

-- FailuresFollowTheWalk, OnlyTheFirstFailureIsReported
#guard polyOf "x" ((x + y) ^ (-1 : ℤ)) == .fault (.term .unknownSymbol)
#guard polyOf "x" (y / x) == .fault .notPolynomial
#guard polyOf "x" (x / y) == .fault (.term .unknownSymbol)
#guard (x ^ 100 * .sym "z" : E).term.map ((ring "x").expand (withExponent 50)) ==
  some (.resourceLimit .exponent)
#guard (.sym "z" + x ^ 100 : E).term.map ((ring "x").expand (withExponent 50)) ==
  some (.fault (.term .unknownSymbol))

-- PolynomialsConvertBackToTerms, ConversionBuildsCanonicalTerms
#guard termOf "x" (mk [(0, -1), (2, 1)]) == answerOf (x ^ 2 - 1)
#guard termOf "x" Poly.zero == answerOf 0
#guard termOf "x" (mk [(1, 3)]) == .value (.product 3 [.symbol "x"])
#guard termOf "x" (mk [(0, -1), (2, 1)]) != answerOf ((x - 1) * (x + 1))

-- DerivativesOfPolynomialsAndTerms, DerivativesThatVanishOrFail
#guard ((ring "x").power rationalRing Limits.default x1 5).bind
  ((ring "x").derivative rationalRing Limits.default) ==
    .value (mk [(0, 5), (1, 20), (2, 30), (3, 20), (4, 5)])
#guard diffs "t" ((t ^ 3 - 2 * t) / 3) (t ^ 2 - 2 / 3)
#guard withPrime 7 fun F =>
  (⟨F, "x"⟩ : PolynomialRing PrimeField).derivative primeRing Limits.default (pr [(7, 1)]) ==
    .value Poly.zero
#guard diffOf "x" (x + y) == some (.fault (.term .unknownSymbol))

-- BinomialVectorExpands and DegreeLimitVectorFails replay `binomial` and
-- `degree_limit_1` above.

-- TermsWithinTheDepthExpand, DeeperTermsFailAtTheEntry
#guard ((x + 1) ^ 2 : E).term.map Term.depth == some 3
#guard ((x + 1) ^ 2 : E).term.map ((ring "x").expand (withDepth 3)) ==
  some (.value (mk [(0, 1), (1, 2), (2, 1)]))
#guard ((x + y) ^ 2 : E).term.map ((ring "x").expand (withDepth 2)) ==
  some (.resourceLimit .depth)
#guard ((x + y) ^ 2 : E).term.map ((ring "x").expand (withDepth 3)) ==
  some (.fault (.term .unknownSymbol))

-- OneProductForEveryCoefficientRing, CrossTermsVanishModuloTwo
#guard (ring "x").multiply rationalRing Limits.default x1 (mk [(0, -1), (1, 1)]) ==
  .value (mk [(0, -1), (2, 1)])
#guard withPrime 5 fun F =>
  (⟨F, "x"⟩ : PolynomialRing PrimeField).multiply primeRing Limits.default (pr [(0, 1), (1, 1)])
    (pr [(0, 4), (1, 1)]) == .value (pr [(0, 4), (2, 1)])
#guard withPrime 2 fun F =>
  (⟨F, "x"⟩ : PolynomialRing PrimeField).power primeRing Limits.default (pr [(0, 1), (1, 1)]) 2 ==
    .value (pr [(0, 1), (2, 1)])

-- BinomialCoefficientsOfAFourthPower, ProductOfXAndXPlusOne
#guard (ring "x").power rationalRing Limits.default x1 4 ==
  .value (mk [(0, 1), (1, 4), (2, 6), (3, 4), (4, 1)])
#guard (ring "x").multiply rationalRing Limits.default (mk [(1, 1)]) x1 ==
  .value (mk [(1, 1), (2, 1)])

-- DivisionsWithRemainder, DivisionByZeroAndByAHigherDegree
#guard Poly.divRem Rationals.field ⟨⟩ (mk [(2, 1)]) (mk [(0, -1), (1, 1)]) ==
  .value (x1, mk [(0, 1)])
#guard withPrime 7 fun F =>
  Poly.divRem PrimeField.field F (pr [(2, 1)]) (pr [(0, 6), (1, 1)]) ==
    .value (pr [(0, 1), (1, 1)], pr [(0, 1)])
#guard Poly.divRem Rationals.field ⟨⟩ (mk [(1, 1)]) Poly.zero == .fault (.field .divisionByZero)
#guard Poly.rem Rationals.field ⟨⟩ (mk [(1, 1)]) Poly.zero == .fault (.field .divisionByZero)
#guard Poly.divRem Rationals.field ⟨⟩ (mk [(0, 1)]) (mk [(1, 1)]) == .value (Poly.zero, mk [(0, 1)])

-- GcdsOfCommonFactors, GcdsWithZeroAndConstants
#guard Poly.monicGcd Rationals.field ⟨⟩ (mk [(0, -1), (2, 1)]) (mk [(0, -1), (1, 1)]) ==
  .value (mk [(0, -1), (1, 1)])
#guard Poly.monicGcd Rationals.field ⟨⟩ (mk [(0, -1), (2, 1)]) (mk [(0, 1), (1, -2), (2, 1)]) ==
  .value (mk [(0, -1), (1, 1)])
#guard Poly.monicGcd Rationals.field ⟨⟩ (mk [(0, 2), (1, 2)]) Poly.zero == .value x1
#guard Poly.monicGcd Rationals.field ⟨⟩ Poly.zero Poly.zero == .value Poly.zero
#guard Poly.monicGcd Rationals.field ⟨⟩ (mk [(1, 1)]) (mk [(0, 3)]) == .value (mk [(0, 1)])

-- ExtendedGcdOfAMultiple, ExtendedGcdsWithZero
#guard Poly.extendedGcd Rationals.field ⟨⟩ (mk [(0, -1), (2, 1)]) (mk [(0, -1), (1, 1)]) ==
  .value ⟨Poly.zero, mk [(0, 1)], mk [(0, -1), (1, 1)]⟩
#guard Poly.extendedGcd Rationals.field ⟨⟩ Poly.zero Poly.zero ==
  .value ⟨Poly.zero, Poly.zero, Poly.zero⟩
#guard Poly.extendedGcd Rationals.field ⟨⟩ (mk [(1, 2)]) Poly.zero ==
  .value ⟨mk [(0, 1 / 2)], Poly.zero, mk [(1, 1)]⟩

-- ModularPowerOfX, ModularPowersByZeroAndConstants, the latter on a few polynomials
#guard Poly.powerMod Rationals.field ⟨⟩ (mk [(1, 1)]) 5 (mk [(0, 1), (2, 1)]) ==
  .value (mk [(1, 1)])
#guard Poly.powerMod Rationals.field ⟨⟩ (mk [(1, 1)]) 5 Poly.zero == .fault (.field .divisionByZero)
#guard [Poly.zero, mk [(0, 2)], x1, mk [(0, -1 / 3), (2, 5), (7, 1)]].all fun a =>
  (List.range 5).all fun k => Poly.powerMod Rationals.field ⟨⟩ a k (mk [(0, 3)]) == .value Poly.zero

-- EvaluationAtTwo, EvaluationVanishesOnAllOfSeven
#guard Poly.eval rationalRing ⟨⟩ (mk [(0, 1), (2, 1)]) (Fraction.ofRat 2) ==
  .value (Fraction.ofRat 5)
#guard withPrime 7 fun F =>
  (List.range 7).all (fun c => Poly.eval primeRing F (pr [(1, 6), (7, 1)]) ⟨c⟩ == .value ⟨0⟩) &&
    pr [(1, 6), (7, 1)] != Poly.zero

-- IntegerPolynomialsReduceModuloSeven, ReductionOutsideTheDomain
#guard withPrime 7 fun F =>
  Poly.map Integers.toPrimeField primeRing ⟨⟩ F ⟨[(0, 9), (2, 1)]⟩ ==
      .value (.mapped (pr [(0, 2), (2, 1)])) &&
    Poly.map Integers.toPrimeField primeRing ⟨⟩ F ⟨[(0, 1), (1, 7)]⟩ ==
      .value (.mapped (pr [(0, 1)]))
#guard withPrime 7 fun F =>
  Poly.map Rationals.toPrimeField primeRing ⟨⟩ F (mk [(0, 1 / 7), (1, 1)]) == .value .notInDomain

end Kalyx.SpecTests.Polynomials
