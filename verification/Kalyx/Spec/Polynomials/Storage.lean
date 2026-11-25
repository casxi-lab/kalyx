module

public import Kalyx.Spec.Polynomials.Basic

/-!
# Polynomials: storage cost and limits

The storage cost of a polynomial and the checks of the limits that every
polynomial passes before an operation returns it (polynomials contract,
"Limits" and "Storage cost"; architecture, "Limits" and "Storage bytes";
POL-R03). The limits are explicit parameters (`Limits`), not a request
context, and the checks state where an operation reports `ResourceLimit`:

1. the degree against `max_exponent` and the width of `i64`, the width of the
   exponents of terms: the effective bound is the smaller of `maxExponent`
   and `2⁶³ - 1` (`checkDegree`, with `Terms.exponentBound`);
2. then the storage cost against `max_nodes` and `max_storage_bytes`, with
   `max_nodes` when both are exceeded (`checkStorage`).

The number of terms is bounded only through the storage cost, at least one
node per term. The context counts the open frames and the reserved
temporaries together with a value; they, the amounts that a `ResourceLimit`
carries, its scope and the saturation of a cost at `u64::MAX` are not part of
this specification.
-/

@[expose] public section

namespace Kalyx.Spec.Polynomials

open Kalyx.Spec.Fields (CoefficientRing Storage)

/-! ## Limits -/

/-- The fields of the limits of a request that the polynomials read:
`max_exponent`, which bounds degrees and exponents; `max_nodes` and
`max_storage_bytes`, which bound the storage cost of each polynomial; and
`max_depth`, which bounds the depth of a term that the expansion takes. The
other fields of kalyx's `Limits` are not read here: `max_integer_bits`
belongs to the coefficient operations, whose results the polynomials pass
on. -/
structure Limits where
  /-- `max_exponent`: the bound on degrees and exponents. -/
  maxExponent : ℕ
  /-- `max_nodes`: the bound on the nodes of a storage cost. -/
  maxNodes : ℕ
  /-- `max_storage_bytes`: the bound on the bytes of a storage cost. -/
  maxStorageBytes : ℕ
  /-- `max_depth`: the bound on the depth of a term. -/
  maxDepth : ℕ
  deriving DecidableEq, Repr

/-- The default limits of a request (context contract): `max_exponent` 4096,
`max_nodes` 8192, `max_storage_bytes` 262144 and `max_depth` 128. -/
def Limits.default : Limits :=
  { maxExponent := Terms.defaultMaxExponent, maxNodes := 8192, maxStorageBytes := 262144,
    maxDepth := 128 }

/-! ## The storage cost -/

/-- The storage cost of the term `c x^d` in a ring whose variable name has `ℓ`
bytes, where `μ` is the cost of the coefficient, its `measure` in the
coefficient ring: `μ` for the degree 0; `μ` with 2 more nodes and `ℓ + 4`
more bytes for the degree 1; and `μ` with 4 more nodes and `ℓ + |d| + 12` more
bytes for a degree `d ≥ 2`, where `|d|` is the bit length of `d`. Over `ℚ`,
where `μ` is `(1, rb(c))`, these are the costs of the term `c x^d` written out
as a term: `(1, rb(c))`, `(3, rb(c) + ℓ + 4)` and
`(5, rb(c) + ℓ + |d| + 12)`. -/
def termCost (μ : Storage) (ℓ : ℕ) : ℕ → Storage
  | 0 => μ
  | 1 => ⟨μ.nodes + 2, μ.bytes + ℓ + 4⟩
  | d + 2 => ⟨μ.nodes + 4, μ.bytes + ℓ + (d + 2).size + 12⟩

/-- The storage cost of the polynomial `a` of the ring `r`, kalyx's
`storage(polynomial)`, with `ℓ` the bytes of the name of the variable:
`(1, 4)` for the zero polynomial; otherwise the costs of its terms
(`termCost`, each with the `measure` of its coefficient in the coefficient
ring), `(1, 4)` for each addition between two terms, and `(0, ℓ)`, the name
once more, when no term has a positive degree. So `x²⁵⁶ - 1` in `x` costs
`(7, 36)`. The cost depends only on the ring and the polynomial: it reads no
limits and cannot fail. -/
def PolynomialRing.storage {P E U : Type} (R : CoefficientRing P E U) (r : PolynomialRing P)
    (a : Poly E) : Storage :=
  let ℓ := r.variableName.utf8ByteSize
  match a.terms with
  | [] => ⟨1, 4⟩
  | t :: ts =>
    let costs := (t :: ts).map fun (d, c) => termCost (R.measure r.coefficients c) ℓ d
    let name := if (t :: ts).all (·.1 == 0) then ℓ else 0
    ⟨(costs.map Storage.nodes).sum + ts.length,
      (costs.map Storage.bytes).sum + 4 * ts.length + name⟩

/-! ## Checks -/

/-- The check of a degree or an exponent `d` under `L`: `ResourceLimit` naming
`max_exponent` when `d` is above the effective bound, the smaller of
`maxExponent` and `2⁶³ - 1`, so that every degree is the exponent of a term;
otherwise `next ()`, the rest of the operation, which is not computed when
the check fails. Degrees and exponents are natural numbers here, so an
amount that kalyx computes beyond `u64::MAX` is exact and above the bound as
well. -/
def checkDegree {α : Type} (L : Limits) (d : ℕ) (next : Unit → PolyResult α) :
    PolyResult α :=
  if Terms.exponentBound L.maxExponent < d then .resourceLimit .exponent else next ()

/-- The check of the storage cost `s` under `L`: `ResourceLimit` naming
`max_nodes` when its nodes are above `maxNodes`, whatever its bytes; then
`ResourceLimit` naming `max_storage_bytes` when its bytes are above
`maxStorageBytes`; otherwise `next ()`, which is not computed when the check
fails. -/
def checkStorage {α : Type} (L : Limits) (s : Storage) (next : Unit → PolyResult α) :
    PolyResult α :=
  if L.maxNodes < s.nodes then .resourceLimit .nodes
  else if L.maxStorageBytes < s.bytes then .resourceLimit .storageBytes
  else next ()

/-- The check of the polynomial `a` of the ring `r` under `L`, before an
operation returns it and for every partial sum of the rows of a product: its
degree (`checkDegree`, nothing for the zero polynomial), then its storage
cost (`checkStorage`); `a` itself when both pass. A polynomial is checked
against the limits that are given, wherever it was built, so one built under
wider limits is checked as part of every result built from it. -/
def PolynomialRing.check {P E U : Type} (R : CoefficientRing P E U) (L : Limits)
    (r : PolynomialRing P) (a : Poly E) : PolyResult (Poly E) :=
  checkDegree L (a.degree.getD 0) fun _ => checkStorage L (r.storage R a) fun _ => .value a

end Kalyx.Spec.Polynomials

end
