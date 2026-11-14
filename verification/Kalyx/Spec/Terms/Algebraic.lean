module

public import Kalyx.Spec.Terms.Call
public import Kalyx.Spec.Fields.NumberField
public import Mathlib.Basic.Complex.Basic

/-!
# Terms: algebraic constants and principal roots

An algebraic constant of rank 1 (TRM-R13) holds the identity `(m, k)` of an
algebraic number (architecture, "Identity"): `m` is the minimal polynomial of
the number over `ℚ`, monic, irreducible and of degree at least 2, and `k` is
the position of the number among the real roots of `m` in ascending order for
the real type, and among all the roots of `m` in the ascending order of the
pair (real part, imaginary part) for the complex type, which holds only
numbers that are not real; positions count from 0. Irreducibility over `ℚ`
and the positions of roots are not decided in this specification, so the
valid identities are a proposition (`Constant.Valid`), and the value of a
constant is a parameter of the semantics.

Two functions fix how rationals and algebraic numbers become terms. The
principal root of a rational has a call as its canonical form, which the
rules of calls normalize cheaply (`principalRoot`; architecture, "Principal
roots of rationals"). An algebraic number becomes a term by five rules
(`Constant.embed`; "Algebraic numbers as terms"), the reverse direction of
that normalization: the rationals, the numbers of degree 2 and the roots of
`x ^ n - q` that the rules name have closed forms, and every other number is
its constant. A canonical term holds an algebraic constant only for an
identity without a closed form (`Constant.hasClosedForm`), so the parsed
`sqrt(2)` and the real number `(x ^ 2 - 2, 1)` are one term.
-/

@[expose] public section

namespace Kalyx.Spec.Terms

open Kalyx.Spec.Fields.QPoly (MonicIrreducible toPoly)

/-! ## Valid identities -/

/-- The real roots of the polynomial of an identity. -/
noncomputable def AlgebraicId.realRoots (id : AlgebraicId) : Finset ℝ :=
  ((toPoly id.minimal).aroots ℝ).toFinset

/-- The complex roots of the polynomial of an identity. -/
noncomputable def AlgebraicId.complexRoots (id : AlgebraicId) : Finset ℂ :=
  ((toPoly id.minimal).aroots ℂ).toFinset

/-- The order in which the roots of a complex identity are counted: `w` comes
before `z` by the pair (real part, imaginary part). -/
def complexBefore (w z : ℂ) : Prop := w.re < z.re ∨ (w.re = z.re ∧ w.im < z.im)

/-- The identity of a real algebraic constant names `x`: `x` is a real root of
`m` with exactly `k` real roots of `m` below it. -/
def AlgebraicId.NamesReal (id : AlgebraicId) (x : ℝ) : Prop :=
  x ∈ id.realRoots ∧ (id.realRoots.filter (· < x)).card = id.index

open Classical in
/-- The identity of a complex algebraic constant names `z`: `z` is a root of
`m` that is not real, with exactly `k` roots of `m` before it by the pair
(real part, imaginary part). -/
def AlgebraicId.NamesComplex (id : AlgebraicId) (z : ℂ) : Prop :=
  z ∈ id.complexRoots ∧ z.im ≠ 0 ∧ (id.complexRoots.filter (complexBefore · z)).card = id.index

/-- A valid constant (TRM-R13): a named constant; or an algebraic constant
whose `m` is monic, irreducible over `ℚ` and of degree at least 2, and whose
identity names a root of its type. Equal values then have equal identities,
and the value is never 0. -/
def Constant.Valid : Constant → Prop
  | .named _ => True
  | .real id => MonicIrreducible id.minimal ∧ 3 ≤ id.minimal.length ∧ ∃ x, id.NamesReal x
  | .complex id => MonicIrreducible id.minimal ∧ 3 ≤ id.minimal.length ∧ ∃ z, id.NamesComplex z

/-! ## Principal roots of rationals -/

/-- The largest `r + s`, with `s` a sum of distinct powers of two below `2 ^ i`,
whose `d`-th power is at most `a`, chosen from the highest bit down. -/
def natRootFrom (d a : ℕ) : ℕ → ℕ → ℕ
  | 0, r => r
  | i + 1, r => natRootFrom d a i (if (r + 2 ^ i) ^ d ≤ a then r + 2 ^ i else r)
  termination_by structural i => i

/-- The integer part of the `d`-th root of `a`, for `d ≥ 1`: the largest `r`
with `r ^ d ≤ a`, which has at most `|a| / d + 1` bits. -/
def natRoot (d a : ℕ) : ℕ := natRootFrom d a (a.size / d + 1) 0

/-- The `d`-th root of a positive rational `q` when `q` is the `d`-th power of a
rational, that is when its numerator and its denominator are `d`-th powers of
natural numbers; none otherwise. -/
def ratRoot? (d : ℕ) (q : ℚ) : Option ℚ :=
  let a := natRoot d q.num.natAbs
  let b := natRoot d q.den
  if a ^ d = q.num.natAbs ∧ b ^ d = q.den then some ((a : ℚ) / b) else none

/-- Step 3 of the normalization of the principal root of a positive rational
`q` of the degree `n`: the divisors `d` of `n` are tried from 2 upwards, each
as long as `q` is a `d`-th power, which replaces `q` and `n` by `q ^ (1/d)` and
`n / d`. A divisor that is not prime never applies, since its prime factors
were tried before it, so these are the replacements by primes, in ascending
order; the end does not depend on the order. Each step raises `d` or divides
`n`, so `2 n` steps are enough. -/
def reduceRoot : ℕ → ℕ → ℚ → ℕ → ℚ × ℕ
  | 0, _, q, n => (q, n)
  | fuel + 1, d, q, n =>
    if n < d then (q, n)
    else
      match (if n % d = 0 then ratRoot? d q else none) with
      | some r => reduceRoot fuel d r (n / d)
      | none => reduceRoot fuel (d + 1) q n
  termination_by structural fuel => fuel

/-- The call of the principal root of `q` of the degree `n`: `sqrt(q)` for the
degree 2, and `rootn(q, n)` otherwise. -/
def rootCall (q : ℚ) (n : ℕ) : Term :=
  if n = 2 then .call ⟨"sqrt", .registered⟩ [.number q]
  else .call ⟨"rootn", .registered⟩ [.number q, .number n]

/-- The principal root of a positive rational `q` of the degree `n ≥ 1` after
step 3: the rational when the degree has become 1, and the call otherwise. -/
def positiveRoot (q : ℚ) (n : ℕ) : Term :=
  match reduceRoot (2 * n) 2 q n with
  | (r, 1) => .number r
  | (r, k) => rootCall r k

/-- The principal root `q ^ (1/n)` of a rational `q` of the degree `n ≥ 1` as a
term, normalized by the steps of the architecture: (1) `n = 1` gives `q`;
(2) `q = 0` gives 0; (3) for `q > 0`, `reduceRoot`; (4) for `q < 0` and
`n = 2`, `i √(-q)`; (5) for `q = -4 t ^ 4` with a rational `t > 0` and `n = 4`,
`t + t i`; (6) any other root is its call. -/
def principalRoot (q : ℚ) (n : ℕ) : Term :=
  if n = 1 then .number q
  else if q = 0 then .number 0
  else if 0 < q then positiveRoot q n
  else if n = 2 then
    match positiveRoot (-q) 2 with
    | .number c => if c = 1 then .constant (.named .i) else .product c [.constant (.named .i)]
    | r => .product 1 [.constant (.named .i), r]
  else
    match (if n = 4 then ratRoot? 4 (-q / 4) else none) with
    | some t => .sum t [(t, .constant (.named .i))]
    | none => rootCall q n

/-! ## Algebraic numbers as terms -/

/-- `a + s r` as a canonical term, for `s ≠ 0` and a term `r` that
`principalRoot` gives for the degree 2 or for a positive rational: a number, a
call, the constant `i` or a product, never a sum. -/
def addScaledRoot (a s : ℚ) : Term → Term
  | .number c => .number (a + s * c)
  | r =>
    let m : ℚ × Term := match r with
      | .product k [f] => (s * k, f)
      | .product k fs => (s * k, .product 1 fs)
      | t => (s, t)
    if a ≠ 0 then .sum a [m]
    else if m.1 = 1 then m.2
    else match m.2 with
      | .product _ fs => .product m.1 fs
      | f => .product m.1 [f]

/-- `(q, n)` when the list `m` is that of `x ^ n - q` with `n ≥ 3`. -/
def binomial? : List ℚ → Option (ℚ × ℕ)
  | c :: rest =>
    if 3 ≤ rest.length ∧ rest = List.replicate (rest.length - 1) 0 ++ [1] then some (-c, rest.length)
    else none
  | [] => none

/-- The term of the algebraic number of the identity `id`, of the complex type
when `complex` holds, and `self` when no closed form applies (architecture,
"Algebraic numbers as terms"): (1) degree 1 gives the number; (2) degree 2,
with `m = x ^ 2 + p x + r`, `a = -p/2` and `Δ = p ^ 2 / 4 - r`, gives
`a ± √Δ`, the principal root of `Δ`, which is `i √(-Δ)` for `Δ < 0`, with the
minus sign for the position 0; (3) for `m = x ^ n - q` with `n ≥ 3`, a real
root is `± rootn(q, n)` for `q > 0`, by its position when `n` is even and the
positive one when `n` is odd, and `-rootn(-q, n)` for `q < 0` and odd `n`, and
the complex root at the position `n - 1` for `q < 0` is `rootn(q, n)`; (4, 5)
every other number is its constant. The roots are those of `principalRoot`. -/
def AlgebraicId.embed (id : AlgebraicId) (complex : Bool) (self : Term) : Term :=
  match id.minimal with
  | [c, _] => .number (-c)
  | [r, p, _] =>
    addScaledRoot (-p / 2) (if id.index = 0 then -1 else 1) (principalRoot (p ^ 2 / 4 - r) 2)
  | m =>
    match binomial? m with
    | some (q, n) =>
      if !complex then
        if 0 < q then
          if n % 2 = 0 ∧ id.index = 0 then addScaledRoot 0 (-1) (principalRoot q n)
          else principalRoot q n
        else if n % 2 = 1 then addScaledRoot 0 (-1) (principalRoot (-q) n)
        else self
      else if q < 0 ∧ id.index = n - 1 then principalRoot q n
      else self
    | none => self

/-- An algebraic number as a term (TRM-R13): a named constant is itself, and an
algebraic number of the real or the complex type is `AlgebraicId.embed`. -/
def Constant.embed : Constant → Term
  | .named c => .constant (.named c)
  | .real id => id.embed false (.constant (.real id))
  | .complex id => id.embed true (.constant (.complex id))

/-- Whether a closed form of the embedding covers a constant, so that it is
never the constant of a canonical term. -/
def Constant.hasClosedForm (c : Constant) : Bool := c.embed != .constant c

end Kalyx.Spec.Terms

end
