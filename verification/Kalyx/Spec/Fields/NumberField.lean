module

public import Kalyx.Spec.Fields.Laws
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Data.List.DropRight
public import Mathlib.RingTheory.AdjoinRoot

/-!
# The number fields

A number field `Q(a)` is the quotient of the rational polynomials by a monic
irreducible polynomial `m`, its minimal polynomial, and `a` is the class of
`X` (numbers contract, FLD-R01, FLD-R02, FLD-R04 and FLD-R05). It is
interpreted in Mathlib's `AdjoinRoot m`, a field since `m` is irreducible.

Polynomials are written as dense lists of their rational coefficients, the
constant first (`QPoly`), with the computable sum, product and long division
of such lists. The defining data of a number field, the parent of its
elements (`NumberField Emb`), are the list of `m` and an embedding, data of a
type `Emb` with a decidable equality that the specification leaves abstract:
fields with the same polynomial and different embeddings are different
parents. A parent also carries the fact that its polynomial is monic and
irreducible over `ℚ` (`QPoly.MonicIrreducible`). The specification does not
decide irreducibility: an implementation establishes it when it builds a
field. Two parents are the same exactly when their defining data are equal
(`sameParent`); no other comparison, such as one of shared handles, takes
part.

An element is the list of its representative, a polynomial in `a`. The
canonical elements (`NumberField.Reduced`) are the lists without trailing
zeros and of degree below that of `m`, so that zero is the empty list. Every
operation returns a canonical element: sums, differences and products of
representatives are reduced modulo `m` by long division
(`NumberField.reduce`), and the inverse of a nonzero element is computed by
the extended Euclidean algorithm on `m` and the element
(`NumberField.inverse`); zero has no inverse and is no divisor, which is
`DivisionByZero`. The zero test always decides. The storage cost of an
element is the parameter `μ` of the coefficient field (`NumberField.field`),
a function of the parent and the element alone. The number fields have no
bit checks in this specification.
-/

@[expose] public section

namespace Kalyx.Spec.Fields

/-! ## Dense rational polynomials -/

namespace QPoly

/-- The rational polynomial that a list of coefficients denotes, the constant
first: `[c₀, c₁, …, cₙ]` denotes `c₀ + c₁ X + … + cₙ Xⁿ`. -/
noncomputable def toPoly : List ℚ → Polynomial ℚ
  | [] => 0
  | c :: l => Polynomial.C c + Polynomial.X * toPoly l

/-- The list without its trailing zeros. It denotes the same polynomial; the
zero polynomial is the empty list. -/
def trim (l : List ℚ) : List ℚ := List.rdropWhile (fun c => decide (c = 0)) l

/-- The sum, coefficient by coefficient. -/
def add : List ℚ → List ℚ → List ℚ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: add p q

/-- The product with the constant `c`. -/
def scale (c : ℚ) (p : List ℚ) : List ℚ := p.map (c * ·)

/-- The difference. -/
def sub (p q : List ℚ) : List ℚ := add p (scale (-1) q)

/-- The product. -/
def mul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)

/-- One step of the long division by `b`, which goes from the highest
coefficient of the dividend down. Given the quotient `q` and the remainder `r`,
a list of `b.length - 1` coefficients, of the coefficients above `c`, the next
remainder is `c + X r` less `t b`, where `t` cancels its coefficient at the
degree of `b`, which is then dropped, and the next quotient is `t + X q`. -/
def divStep (b : List ℚ) (c : ℚ) (qr : List ℚ × List ℚ) : List ℚ × List ℚ :=
  let t := qr.2.getLastD c / b.getLastD 0
  (t :: qr.1, (add (c :: qr.2) (scale (-t) b)).dropLast)

/-- The long division of `p` by `b`, the list of a nonzero polynomial without
trailing zeros: the quotient and the remainder, whose degree is below that of
`b`, both without trailing zeros. -/
def divMod (p b : List ℚ) : List ℚ × List ℚ :=
  let qr := p.foldr (divStep b) ([], List.replicate (b.length - 1) 0)
  (trim qr.1, trim qr.2)

/-- At most `fuel` steps of the extended Euclidean algorithm. From the
remainders `r₀` and `r₁` and their cofactors `s₀` and `s₁`, a step divides
`r₀` by `r₁`, with the quotient `q`, and goes on with the remainders `r₁` and
`r₀ - q r₁` and the cofactors `s₁` and `s₀ - q s₁`. At a zero remainder `r₁`,
or when the steps are spent, the result is `r₀` with its cofactor `s₀`.
Started from `m` with the cofactor `0` and `a` with the cofactor `1`, every
remainder is congruent modulo `m` to its cofactor times `a`, and since the
degrees of the remainders decrease, a zero remainder comes within `m.length`
steps when `a` is of lower degree than `m`; `r₀` is then a greatest common
divisor of `m` and `a`. -/
def euclid : ℕ → List ℚ → List ℚ → List ℚ → List ℚ → List ℚ × List ℚ
  | 0, r₀, s₀, _, _ => (r₀, s₀)
  | fuel + 1, r₀, s₀, r₁, s₁ =>
    if r₁ = [] then (r₀, s₀)
    else
      let qr := divMod r₀ r₁
      euclid fuel r₁ s₁ qr.2 (sub s₀ (mul qr.1 s₁))

/-- `m` is the list of a monic polynomial, whose last coefficient is `1`, that
is irreducible over `ℚ`. -/
def MonicIrreducible (m : List ℚ) : Prop :=
  m.getLast? = some 1 ∧ Irreducible (toPoly m)

end QPoly

/-! ## Number fields -/

/-- A number field, the parent of its elements: its defining data, the list of
its minimal polynomial and its embedding, data of the type `Emb` that the
specification leaves abstract, with the fact that the polynomial is monic and
irreducible over `ℚ`. The generator has no name in these data. -/
structure NumberField (Emb : Type) where
  /-- The coefficients of the minimal polynomial, the constant first. -/
  minimal : List ℚ
  /-- The embedding. -/
  embedding : Emb
  /-- The minimal polynomial is monic and irreducible. -/
  monicIrreducible : QPoly.MonicIrreducible minimal
  deriving DecidableEq, Repr

namespace NumberField

/-- The canonical elements of the number field of the minimal polynomial `m`
(FLD-R01): the lists without trailing zeros of the polynomials of degree below
that of `m`. Zero is the empty list. -/
def Reduced (m e : List ℚ) : Prop := e.getLast? ≠ some 0 ∧ e.length < m.length

/-- The canonical element of the class of the polynomial `p` modulo `m`: the
remainder of the long division of `p` by `m`. -/
def reduce (m p : List ℚ) : List ℚ := (QPoly.divMod p m).2

/-- The rational `q` as an element: the constant polynomial, reduced. -/
def ofRat (m : List ℚ) (q : ℚ) : List ℚ := reduce m [q]

/-- The generator `a`: the polynomial `X`, reduced. -/
def generator (m : List ℚ) : List ℚ := reduce m [0, 1]

/-- The additive inverse, reduced. -/
def negate (m a : List ℚ) : List ℚ := reduce m (QPoly.scale (-1) a)

/-- The sum, reduced. -/
def add (m a b : List ℚ) : List ℚ := reduce m (QPoly.add a b)

/-- The difference, reduced. -/
def subtract (m a b : List ℚ) : List ℚ := reduce m (QPoly.sub a b)

/-- The product, reduced modulo `m`. -/
def multiply (m a b : List ℚ) : List ℚ := reduce m (QPoly.mul a b)

/-- The inverse (FLD-R02): zero has none, which is `DivisionByZero`. For a
nonzero canonical element `a` of a field, the extended Euclidean algorithm on
`m` and `a` ends with a greatest common divisor that is a nonzero constant `g`,
since `m` is irreducible, and with its cofactor `s`, so that `s a` is congruent
to `g` modulo `m`; the inverse is `s / g`, reduced. -/
def inverse (m a : List ℚ) : Outcome (List ℚ) :=
  if a = [] then .fault .divisionByZero
  else
    let rs := QPoly.euclid m.length m [] a [1]
    .value (reduce m (QPoly.scale (rs.1.headD 0)⁻¹ rs.2))

/-- The quotient: the product with the inverse of the divisor, so that a zero
divisor is `DivisionByZero`. -/
def divide (m a b : List ℚ) : Outcome (List ℚ) := (inverse m b).map (multiply m a)

/-- The zero test (FLD-R04): a canonical element is zero exactly when it is the
empty list, so the test always decides. -/
def zeroTest (a : List ℚ) : ZeroTest Empty := ZeroTest.ofDecide (a = [])

/-- The number fields as a coefficient field, with the storage cost `μ` of an
element: parents are the same exactly when their defining data are equal
(FLD-R05); `zero`, `one` and `fromInteger` are constant polynomials; the other
operations are those above on the minimal polynomial of the parent; the zero
test always decides. -/
def field (Emb : Type) [DecidableEq Emb] (μ : NumberField Emb → List ℚ → Storage) :
    CoefficientField (NumberField Emb) (List ℚ) Empty where
  sameParent F G := decide (F = G)
  zero _ := []
  one F := NumberField.ofRat F.minimal 1
  fromInteger F n := NumberField.ofRat F.minimal n
  negate F a := .value (NumberField.negate F.minimal a)
  add F a b := .value (NumberField.add F.minimal a b)
  subtract F a b := .value (NumberField.subtract F.minimal a b)
  multiply F a b := .value (NumberField.multiply F.minimal a b)
  zeroTest _ a := .value (NumberField.zeroTest a)
  measure := μ
  inverse F a := NumberField.inverse F.minimal a
  divide F a b := NumberField.divide F.minimal a b

/-- The field `Q(a)` of the parent `F` as Mathlib knows it. -/
abbrev Carrier {Emb : Type} (F : NumberField Emb) : Type :=
  AdjoinRoot (QPoly.toPoly F.minimal)

/-- The interpretation of the number fields: an element denotes the class of
its polynomial modulo the minimal polynomial, and the reduced elements are
canonical. -/
noncomputable def model (Emb : Type) : Model (NumberField Emb) (List ℚ) Carrier :=
  fun F => ⟨fun e => AdjoinRoot.mk (QPoly.toPoly F.minimal) (QPoly.toPoly e),
    Reduced F.minimal⟩

end NumberField

end Kalyx.Spec.Fields

end
