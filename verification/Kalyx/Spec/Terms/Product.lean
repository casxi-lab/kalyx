module

public import Kalyx.Spec.Terms.Sum

/-!
# Terms: products

The canonical product of a list of terms (terms contract, "Products";
architecture, "Canonical forms", "Constants", "Rules of the call
constructor"; TRM-R01, TRM-R04 to TRM-R06, TRM-R13, TRM-R14), under an
explicit `maxExponent`:

1. **Flattening** (`factorParts`): a number multiplies into the
   coefficient, which starts at 1; a product multiplies its coefficient in
   and gives its factors; a sum `s = c · p` multiplies its content `c` in
   and gives the item `(p, 1)` of its primitive part; a one `(b⁻¹)⁰` is set
   aside; a power `b ^ k` with `k ≠ 0` gives the item `(b, k)`; any other
   term `t`, a constant, a symbol or a call, the item `(t, 1)`.
2. **Merging by key** (`mergeItems`): items of one key add their exponents.
   The key of `(b, k)` is `b` and the sign of `k`, but the key of a constant
   is its base alone, so exponents of both signs merge over a constant:
   `x² x⁻¹` keeps two factors while `π π⁻¹ = 1`. Every exponent of a merged
   item is checked against `maxExponent`.
3. **Constants and roots** (`reduceItem`): an exponent 0, which only a
   constant can reach, drops its item, since `c⁰ = 1`. The powers of `i`
   reduce by the exponent modulo 4 to 1, `i`, `-1` and `-i`, the sign going
   into the coefficient. The powers of roots: for a root `ⁿ√u` of a literal
   degree `n` (`sqrt(u)` of degree 2, `rootn(u, n)` with a positive integer
   `n`) and an exponent `k ≥ n`, `(ⁿ√u)ᵏ = u ^ ⌊k/n⌋ (ⁿ√u) ^ (k mod n)`:
   the item keeps `k mod n` and the flattening of `u ^ ⌊k/n⌋` returns to
   the work list, so its items merge with the others. A negative exponent
   leaves a root as it is. These rules of the term core are written out,
   not read from the registry rules.
4. **Zero coefficient**: the product is the zero witness of the maximal
   elements of `N` of the factors and of the ones set aside, or 0.
5. **Ones**: otherwise the bases that the ones set aside hold with a
   negative exponent and that the factors do not hold with one are kept by
   the ones of their maximal elements, which join the factors.
6. **Order**: the factors are sorted by key (`Key.cmp`).
7. **Assembly** (`assembleProduct`): no factor gives the coefficient; the
   coefficient 1 and one factor give that factor; another coefficient and
   one factor that is a sum give that sum scaled by the coefficient;
   anything else is a product node.

Merging and the rules of step 3 run in rounds (`settleItems`): a round
sorts and merges the items, checks their exponents and reduces them, and
the items that the powers of roots return start the next round. The items
that a round returns lie inside the radicands of the roots that gave them,
so their depth is smaller, and one round more than the largest depth of the
items ends the rounds; running out of rounds is `Internal`.

A product takes values only: a condition among its operands fails with
`Syntax`. A product never fails with `DivisionByZero`.
-/

@[expose] public section

namespace Kalyx.Spec.Terms

/-! ## Flattening -/

/-- The parts of a product being built: its coefficient, its items `(b, k)`,
each the factor `b ^ k`, and the ones `(b⁻¹)⁰` set aside. -/
structure ProductParts where
  /-- The coefficient. -/
  coefficient : ℚ
  /-- The items, each a base and its exponent. -/
  items : List (Term × ℤ)
  /-- The ones set aside. -/
  ones : List Term

/-- The parts of the empty product: the coefficient 1. -/
def ProductParts.unit : ProductParts := ⟨1, [], []⟩

/-- The parts of two products together: the coefficients multiplied, the
items and the ones in order. -/
def ProductParts.append (p q : ProductParts) : ProductParts :=
  ⟨p.coefficient * q.coefficient, p.items ++ q.items, p.ones ++ q.ones⟩

/-- The parts of the power `t ^ q`, `q ≥ 1`, of a term `t` that is neither a
number nor a product: of a sum, the content to the power `q` and the item
`(p, q)` of its primitive part; a one, set aside, since every power of a one
is the one itself; of a power `b ^ j`, the item `(b, j q)`, whose exponent
is checked; and of any other term, the item `(t, q)`. -/
def itemParts (maxExponent : ℕ) (q : ℤ) : Term → Result ProductParts
  | .sum c ms => .value ⟨sumContent c ms ^ q, [(primitivePart c ms, q)], []⟩
  | .power b j =>
    if j = 0 then .value ⟨1, [], [.power b j]⟩
    else checkExponent maxExponent (j * q) fun _ => .value ⟨1, [(b, j * q)], []⟩
  | t => .value ⟨1, [(t, q)], []⟩

/-- The parts of the power `t ^ q`, `q ≥ 1`, of a canonical term `t`: of a
number, its power; of a product, its coefficient to the power `q` and the
parts of each factor; of any other term, `itemParts`. With `q = 1` these are
the parts that an operand gives. -/
def factorParts (maxExponent : ℕ) (q : ℤ) : Term → Result ProductParts
  | .number r => .value ⟨r ^ q, [], []⟩
  | .product c fs => do
    let ps ← fs.mapM (itemParts maxExponent q)
    pure (ps.foldl ProductParts.append ⟨c ^ q, [], []⟩)
  | t => itemParts maxExponent q t

/-- The parts that the operands `ts` of a product give, in order. -/
def productParts (maxExponent : ℕ) (ts : List Term) : Result ProductParts := do
  let ps ← ts.mapM (factorParts maxExponent 1)
  pure (ps.foldl ProductParts.append ProductParts.unit)

/-! ## Merging, constants and roots -/

/-- The items sorted by key, with the exponents of equal keys added. -/
def mergeItems (o : Orders) (items : List (Term × ℤ)) : List (Term × ℤ) :=
  mergeAdjacent (fun x y => if Key.of x.1 x.2 = Key.of y.1 y.2 then some (x.1, x.2 + y.2) else none)
    (sortBy (fun x y => Key.cmp o (Key.of x.1 x.2) (Key.of y.1 y.2)) items)

/-- The constant `i`. -/
def Term.imaginaryUnit : Term := .constant (.named .i)

/-- The radicand and the literal degree of a root: `sqrt(u)` has the
degree 2, and `rootn(u, n)` the degree `n` when `n` is a number that is a
positive integer; both are calls of the class `Registered`. Any other term,
`rootn` with another degree included, is no root here. -/
def rootOf : Term → Option (Term × ℕ)
  | .call h [u] => if h = ⟨"sqrt", .registered⟩ then some (u, 2) else none
  | .call h [u, .number n] =>
    if h = ⟨"rootn", .registered⟩ ∧ n.den = 1 ∧ 0 < n then some (u, n.num.toNat) else none
  | _ => none

/-- A merged item `(b, k)`: its exponent is checked, and then it is dropped
for `k = 0`; for `b = i`, the coefficient `-1` when `k mod 4` is 2 or 3 and
the item `(i, 1)` when `k` is odd; for a root `b = ⁿ√u` and `k ≥ n`, the
parts of `u ^ ⌊k/n⌋` and the item `(b, k mod n)` unless `k mod n = 0`; and
otherwise the item itself. The result holds the settled parts and the items
that return to the work list. -/
def reduceItem (maxExponent : ℕ) : Term × ℤ → Result (ProductParts × List (Term × ℤ))
  | (b, k) => checkExponent maxExponent k fun _ =>
    if k = 0 then .value (ProductParts.unit, [])
    else if b = Term.imaginaryUnit then
      let r := k % 4
      let sign : ℚ := if r = 2 ∨ r = 3 then -1 else 1
      .value (⟨sign, if r = 1 ∨ r = 3 then [(b, 1)] else [], []⟩, [])
    else match rootOf b with
      | some (u, n) =>
        if (n : ℤ) ≤ k then do
          let p ← factorParts maxExponent (k / n) u
          pure (⟨p.coefficient, if k % n = 0 then [] else [(b, k % n)], p.ones⟩, p.items)
        else .value (⟨1, [(b, k)], []⟩, [])
      | none => .value (⟨1, [(b, k)], []⟩, [])

/-- The rounds of merging and reduction, at most `fuel` of them: each round
merges the items of `p`, reduces each merged item, and ends the rounds when
no item returns; running out of rounds is `Internal`. -/
def settleItems (o : Orders) (maxExponent : ℕ) : ℕ → ProductParts → Result ProductParts
  | 0, _ => .fault .internal
  | fuel + 1, p => do
    let rs ← (mergeItems o p.items).mapM (reduceItem maxExponent)
    let settled := rs.foldl (fun acc r => acc.append r.1) ⟨p.coefficient, [], p.ones⟩
    let back := (rs.map Prod.snd).flatten
    if back.isEmpty then pure settled
    else
      settleItems o maxExponent fuel ⟨settled.coefficient, settled.items ++ back, settled.ones⟩
  termination_by structural fuel _ => fuel

/-! ## Witnesses, order and assembly -/

/-- The factor of an item `(b, k)`: the base for the exponent 1, and the
power `b ^ k` otherwise. -/
def itemFactor (x : Term × ℤ) : Term := if x.2 = 1 then x.1 else .power x.1 x.2

/-- The product of a coefficient other than 0 and canonical factors in
order: the coefficient without factors; the factor for the coefficient 1
and one factor; a sum scaled by the coefficient for one factor that is a
sum; otherwise a product node. -/
def assembleProduct (c : ℚ) : List Term → Term
  | [] => .number c
  | [f] =>
    if c = 1 then f
    else match f with
      | .sum a ms => scaleSum c a ms
      | f => .product c [f]
  | fs => .product c fs

/-- The canonical product of the parts `p`: the rounds of merging and
reduction; then for the coefficient 0 the zero witness of the factors and
the ones; and otherwise the ones that keep the bases the factors do not
hold, the factors sorted by key, and the assembly. -/
def buildProduct (o : Orders) (maxExponent : ℕ) (p : ProductParts) : Result Term := do
  let p ← settleItems o maxExponent (Term.depthList (p.items.map Prod.fst) + 1) p
  let factors := p.items.map itemFactor
  if p.coefficient = 0 then
    pure (zeroWitness (maxBases o (Term.negBasesList (factors ++ p.ones))))
  else
    let kept := maxBases o (uncovered (Term.negBasesList p.ones) (Term.negBasesList factors))
    pure (assembleProduct p.coefficient
      (sortBy (fun f g => Key.cmp o f.key g.key) (factors ++ kept.map Term.oneOf)))

/-- The canonical product of the terms `ts` (`Term::product`), whose order
is `o`, under `maxExponent`. A condition among the operands fails with
`Syntax`; an exponent beyond the bound fails with `ResourceLimit` naming
`max_exponent`. -/
def mkProduct (o : Orders) (maxExponent : ℕ) (ts : List Term) : Result Term :=
  if ts.any Term.isCondition then .fault (.syntax none)
  else do
    let p ← productParts maxExponent ts
    buildProduct o maxExponent p

end Kalyx.Spec.Terms

end
