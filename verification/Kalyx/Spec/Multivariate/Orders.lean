module

public import Kalyx.Spec.Multivariate.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finsupp.MonomialOrder

/-!
# Multivariate polynomials: monomial orders

The four monomial orders of a ring (FLD-R06), each in two forms on the
exponent vectors of `n` variables:

* the strict order, a proposition (`LexLT`, `GrLexLT`, `GrevLexLT`,
  `BlockLT`, and `OrderKind.Lt` by the order of a ring), which says what the
  order is;
* the comparison, a computable function that returns an `Ordering`
  (`compareLex`, `compareGrLex`, `compareGrevLex`, `compareBlock`, and
  `OrderKind.compare`), by which the operations sort the terms of a
  polynomial.

`lex` compares the exponents from the first variable; `grlex` compares the
total degree first and then as `lex`; `grevlex` compares the total degree
first and then lets the smaller exponent at the last variable where the
exponents differ belong to the greater monomial; and the block order
`block k` compares the first `k` variables by `grevlex` and, when they are
equal, the last `n - k` variables by `grevlex`. The strict orders of
`grevlex` and of the blocks are taken over from the specification of the
earlier implementation as definitions only (`PORTING.md`); there the
exponent vectors were the vectors of Mathlib, here they are the functions
`Exponents n`, which denote them. That each order is a strict total order,
compatible with the product of monomials, well founded, with the constant
monomial least, that a block order eliminates its first block, and that the
comparisons agree with the strict orders are statements about these
definitions. So is that each order is the strict order of a monomial order of
Mathlib, `MonomialOrder (Fin n)`, through `Exponents.toFinsupp`
(`OrderKind.Agrees`); this specification builds no such order.
-/

@[expose] public section

namespace Kalyx.Spec.Multivariate

/-! ## The blocks of a vector -/

namespace Exponents

variable {n : ℕ}

/-- The exponents of the first `k` variables, the first block of the block
order `block k`. -/
def firstBlock (k : Fin (n + 1)) (a : Exponents n) : Exponents k :=
  fun i => a (Fin.castLE (Nat.le_of_lt_succ k.isLt) i)

/-- The exponents of the last `n - k` variables, the second block of the block
order `block k`: the exponent at the position `j` of the block is that of the
variable at the position `k + j` of the ring. -/
def secondBlock (k : Fin (n + 1)) (a : Exponents n) : Exponents (n - k) :=
  fun j => a (Fin.cast (Nat.add_sub_cancel' (Nat.le_of_lt_succ k.isLt)) (Fin.natAdd k j))

end Exponents

/-! ## The strict orders

`Prod.Lex r s (x₁, x₂) (y₁, y₂)` holds when `r x₁ y₁`, or `x₁ = y₁` and
`s x₂ y₂`: the first component decides, and the second only on a tie. -/

variable {n : ℕ}

/-- `lex`: `a` is below `b` when, at the first variable where they differ,
`a` has the smaller exponent. -/
def LexLT (a b : Exponents n) : Prop :=
  ∃ j, (∀ d, d < j → a d = b d) ∧ a j < b j

/-- Reverse lexicographic comparison: at the last variable where two vectors
differ, the smaller exponent leads, that is, belongs to the greater
vector. -/
def RevLexLT (a b : Exponents n) : Prop :=
  ∃ j, (∀ d, j < d → a d = b d) ∧ b j < a j

/-- `grlex`: the total degree first, then `lex`. -/
def GrLexLT (a b : Exponents n) : Prop :=
  Prod.Lex (· < ·) LexLT (a.degree, a) (b.degree, b)

/-- `grevlex`: the total degree first, then reverse lexicographic. -/
def GrevLexLT (a b : Exponents n) : Prop :=
  Prod.Lex (· < ·) RevLexLT (a.degree, a) (b.degree, b)

/-- The block order `block k`: the first `k` variables by `grevlex`; when they
are equal, the last `n - k` variables by `grevlex`. -/
def BlockLT (k : Fin (n + 1)) (a b : Exponents n) : Prop :=
  Prod.Lex GrevLexLT GrevLexLT (a.firstBlock k, a.secondBlock k) (b.firstBlock k, b.secondBlock k)

/-- The strict order of the monomial order `o`: `a` is below `b`. -/
def OrderKind.Lt : OrderKind n → Exponents n → Exponents n → Prop
  | .lex => LexLT
  | .grlex => GrLexLT
  | .grevlex => GrevLexLT
  | .block k => BlockLT k

/-! ## The comparisons

`o₁.then o₂` is `o₁` unless it is `eq`, and then `o₂`. -/

/-- The comparison of `lex`: the exponents of the first variable, then, when
they are equal, the remaining variables in their order. -/
def compareLex : {n : ℕ} → Exponents n → Exponents n → Ordering
  | 0, _, _ => .eq
  | _ + 1, a, b => (compare (a 0) (b 0)).then (compareLex (Fin.tail a) (Fin.tail b))
  termination_by structural n => n

/-- The reverse lexicographic comparison: the exponents of the last variable,
the smaller one belonging to the greater vector, then, when they are equal,
the variables before it from the last backwards. -/
def compareRevLex : {n : ℕ} → Exponents n → Exponents n → Ordering
  | 0, _, _ => .eq
  | n + 1, a, b =>
    (compare (b (Fin.last n)) (a (Fin.last n))).then (compareRevLex (Fin.init a) (Fin.init b))
  termination_by structural n => n

/-- The comparison of `grlex`: the total degrees, then `compareLex`. -/
def compareGrLex (a b : Exponents n) : Ordering :=
  (compare a.degree b.degree).then (compareLex a b)

/-- The comparison of `grevlex`: the total degrees, then `compareRevLex`. -/
def compareGrevLex (a b : Exponents n) : Ordering :=
  (compare a.degree b.degree).then (compareRevLex a b)

/-- The comparison of the block order `block k`: the first blocks by
`compareGrevLex`, then, when they are equal, the second blocks by
`compareGrevLex`. -/
def compareBlock (k : Fin (n + 1)) (a b : Exponents n) : Ordering :=
  (compareGrevLex (a.firstBlock k) (b.firstBlock k)).then
    (compareGrevLex (a.secondBlock k) (b.secondBlock k))

/-- The comparison of the monomial order `o`, by which the monomials of a
ring are sorted: `lt` when `a` is below `b`, `eq` when they are equal,
and `gt` when `a` is above `b`. -/
def OrderKind.compare : OrderKind n → Exponents n → Exponents n → Ordering
  | .lex => compareLex
  | .grlex => compareGrLex
  | .grevlex => compareGrevLex
  | .block k => compareBlock k

/-! ## Monomial orders of Mathlib -/

/-- The monomial order `m` of Mathlib on the variables `Fin n` orders the
monomials as `o` does: through `Exponents.toFinsupp`, the strict order of `m`
is the strict order of `o`. Two such orders have the same strict order, so
they give a polynomial of Mathlib the same leading monomial and the same
leading coefficient. -/
def OrderKind.Agrees (o : OrderKind n) (m : MonomialOrder (Fin n)) : Prop :=
  ∀ a b : Exponents n, m.toSyn a.toFinsupp < m.toSyn b.toFinsupp ↔ o.Lt a b

end Kalyx.Spec.Multivariate

end
