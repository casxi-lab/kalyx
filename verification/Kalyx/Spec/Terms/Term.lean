module

public import Kalyx.Spec.Terms.Basic

/-!
# Terms: kinds, size, depth and bytes

`Term` is the one representation of the term core: a tree of eight kinds,
ranked 0 to 7 in the total order (terms contract, "Kinds and the total
order"; architecture, "Kinds and order"): numbers, constants, symbols, calls,
integer powers, products, sums and conditions. Ranks 0 to 6 are the value
classes and rank 7 the conditions (TRM-R15). A number holds Mathlib's `ℚ`,
reduced by construction, so its canonical form is that of the rationals of
the coefficient fields. A monomial of a sum is the pair of its coefficient
and its core. `undefined` is not a term.

The type holds every tree, canonical or not: the canonical-form predicate
says which trees are canonical, and the constructors of the term core are
functions that return canonical terms. Children are lists in their stored
order. A shared subterm and a separate copy are one value, so sharing is
invisible. Equality is structural: the `DecidableEq` instance is written out,
since Lean derives it for no nested inductive type, and `==` on terms is that
equality.

The tree size, the depth and the logical bytes follow the terms contract
("Size, depth and storage"); the bytes of constants, calls and conditions,
whose formulas are fixed with these kinds, are parameters (`ByteParams`).
-/

@[expose] public section

namespace Kalyx.Spec.Terms

/-! ## Calls, constants and the shapes of conditions -/

/-- The class of a call: `Registered` for the functions of the function
registry, `Formal` for the special forms `piecewise`, `derivative` and
`substitute`, which the registry does not hold. -/
inductive CallClass where
  /-- A function of the function registry. -/
  | registered
  /-- A special form. -/
  | formal
  deriving DecidableEq, Repr

/-- The head of a call, `Head { name, class }`: the name and the class. -/
structure Head where
  /-- The name of the function or of the special form. -/
  name : String
  /-- The class. -/
  callClass : CallClass
  deriving DecidableEq, Repr

/-- The named constants, `π` and `i`. They are ordered by their names
(`NamedConstant.name`), not by this declaration. -/
inductive NamedConstant where
  /-- The imaginary unit `i`. -/
  | i
  /-- `π`. -/
  | pi
  deriving DecidableEq, Repr

/-- The name of a named constant: `i` and `pi`. -/
def NamedConstant.name : NamedConstant → String
  | .i => "i"
  | .pi => "pi"

/-- The identity `(m, k)` of an algebraic number (architecture, "Identity"):
the list of the coefficients of its minimal polynomial `m`, the constant
first, as in the dense polynomials of the number fields, and its position `k`
among the roots of `m` in the order of its type, counted from 0. The data are
any list and any position; which identities are valid, a monic irreducible
`m` of degree at least 2 and a position among its roots, is stated apart. -/
structure AlgebraicId where
  /-- The coefficients of the minimal polynomial, the constant first. -/
  minimal : List ℚ
  /-- The position among the roots. -/
  index : ℕ
  deriving DecidableEq, Repr

/-- A constant of rank 1 (TRM-R13): a named constant, or an algebraic constant
of the real or the complex type, by its identity. A real algebraic number is
never of the complex type. -/
inductive Constant where
  /-- `π` or `i`. -/
  | named (c : NamedConstant)
  /-- A real algebraic number: `k` counts the real roots of `m` in ascending
  order. -/
  | real (id : AlgebraicId)
  /-- A complex algebraic number that is not real: `k` counts all the roots
  of `m` in the ascending order of the pair (real part, imaginary part). -/
  | complex (id : AlgebraicId)
  deriving DecidableEq, Repr

/-- The relations of a comparison: `eq`, `ne`, `lt`, `le`, `gt` and `ge` for
`==`, `!=`, `<`, `<=`, `>` and `>=`. -/
inductive Relation where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr

/-- The shape of a condition (architecture, "Conditions"), with its relation
or its property: a truth value; a comparison of two values; a property
predicate `is_<property>(u)` of one value, by the name of the property; the
predicate `defined(u)`; and the connectives `not` of one condition and `and`
and `or` of two or more. The number and the classes of the operands of each
shape are checked by the constructor of conditions. -/
inductive CondShape where
  /-- `true` or `false`, without operands. -/
  | truth (value : Bool)
  /-- A comparison of two values. -/
  | comparison (relation : Relation)
  /-- A property predicate of one value. -/
  | predicate (property : String)
  /-- `defined(u)`, of one value. -/
  | defined
  /-- `not`, of one condition. -/
  | not
  /-- `and`, of two or more conditions. -/
  | and
  /-- `or`, of two or more conditions. -/
  | or
  deriving DecidableEq, Repr

/-! ## Terms -/

/-- A term of kalyx, of one of the eight kinds; the rank of each is
`Term.rank`. -/
inductive Term where
  /-- A number, rank 0. -/
  | number (value : ℚ)
  /-- A constant, rank 1. -/
  | constant (c : Constant)
  /-- A symbol, rank 2, by its name. -/
  | symbol (name : String)
  /-- A call, rank 3: its head and its arguments in their given order. -/
  | call (head : Head) (args : List Term)
  /-- An integer power `b ^ k`, rank 4. -/
  | power (base : Term) (exponent : ℤ)
  /-- A product, rank 5: its coefficient and its factors. -/
  | product (coefficient : ℚ) (factors : List Term)
  /-- A sum, rank 6: its constant and its monomials, each the pair of its
  coefficient and its core. -/
  | sum (constant : ℚ) (monomials : List (ℚ × Term))
  /-- A condition, rank 7: its shape and its operands. -/
  | condition (shape : CondShape) (operands : List Term)

instance : Inhabited Term := ⟨.number 0⟩

-- Structural equality, by mutual structural recursion. The constructors are
-- compared by their index first, so only the eight cases of one kind are written.
mutual

/-- Structural equality of terms, decided. -/
def Term.decEq (a b : Term) : Decidable (a = b) :=
  if hc : a.ctorIdx = b.ctorIdx then
    match a, b, hc with
    | .number p, .number q, _ =>
      if h : p = q then isTrue (h ▸ rfl) else isFalse (fun e => h (Term.number.inj e))
    | .constant c, .constant d, _ =>
      if h : c = d then isTrue (h ▸ rfl) else isFalse (fun e => h (Term.constant.inj e))
    | .symbol s, .symbol r, _ =>
      if h : s = r then isTrue (h ▸ rfl) else isFalse (fun e => h (Term.symbol.inj e))
    | .call h as, .call g bs, _ =>
      match _root_.decEq h g, Term.decEqList as bs with
      | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
      | isFalse n, _ => isFalse (fun e => n (Term.call.inj e).1)
      | _, isFalse n => isFalse (fun e => n (Term.call.inj e).2)
    | .power b k, .power c l, _ =>
      match Term.decEq b c, _root_.decEq k l with
      | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
      | isFalse n, _ => isFalse (fun e => n (Term.power.inj e).1)
      | _, isFalse n => isFalse (fun e => n (Term.power.inj e).2)
    | .product a fs, .product b gs, _ =>
      match _root_.decEq a b, Term.decEqList fs gs with
      | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
      | isFalse n, _ => isFalse (fun e => n (Term.product.inj e).1)
      | _, isFalse n => isFalse (fun e => n (Term.product.inj e).2)
    | .sum a ms, .sum b ns, _ =>
      match _root_.decEq a b, Term.decEqPairs ms ns with
      | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
      | isFalse n, _ => isFalse (fun e => n (Term.sum.inj e).1)
      | _, isFalse n => isFalse (fun e => n (Term.sum.inj e).2)
    | .condition s xs, .condition r ys, _ =>
      match _root_.decEq s r, Term.decEqList xs ys with
      | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
      | isFalse n, _ => isFalse (fun e => n (Term.condition.inj e).1)
      | _, isFalse n => isFalse (fun e => n (Term.condition.inj e).2)
  else isFalse (fun e => hc (congrArg Term.ctorIdx e))
  termination_by structural a

/-- Equality of lists of terms, decided. -/
def Term.decEqList : (as bs : List Term) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse nofun
  | _ :: _, [] => isFalse nofun
  | t :: ts, u :: us =>
    match Term.decEq t u, Term.decEqList ts us with
    | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
    | isFalse n, _ => isFalse (fun e => n (List.cons.inj e).1)
    | _, isFalse n => isFalse (fun e => n (List.cons.inj e).2)
  termination_by structural as _ => as

/-- Equality of lists of monomials, decided. -/
def Term.decEqPairs : (ms ns : List (ℚ × Term)) → Decidable (ms = ns)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse nofun
  | _ :: _, [] => isFalse nofun
  | (a, t) :: ts, (b, u) :: us =>
    match _root_.decEq a b, Term.decEq t u, Term.decEqPairs ts us with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (h₁ ▸ h₂ ▸ h₃ ▸ rfl)
    | isFalse n, _, _ => isFalse (fun e => n (Prod.mk.inj (List.cons.inj e).1).1)
    | _, isFalse n, _ => isFalse (fun e => n (Prod.mk.inj (List.cons.inj e).1).2)
    | _, _, isFalse n => isFalse (fun e => n (List.cons.inj e).2)
  termination_by structural ms _ => ms

end

instance : DecidableEq Term := Term.decEq

/-- The rank of the kind of a term, from 0 for numbers to 7 for conditions. -/
def Term.rank : Term → ℕ
  | .number _ => 0
  | .constant _ => 1
  | .symbol _ => 2
  | .call .. => 3
  | .power .. => 4
  | .product .. => 5
  | .sum .. => 6
  | .condition .. => 7

/-- Whether a term is a condition, of rank 7, rather than a value. -/
def Term.isCondition : Term → Bool
  | .condition .. => true
  | _ => false

/-- Whether a term is a constant. -/
def Term.isConstant : Term → Bool
  | .constant _ => true
  | _ => false

/-! ## Size, depth and bytes

The tree size of a term is its number of nodes, a shared subterm counted once
for each occurrence; coefficients, constants and exponents stored in a node
add no nodes. A number and a symbol have the depth 1, and any other node one
more than the largest depth of its children, so a node without children, such
as a constant, has the depth 1 too (TRM-R09). -/

mutual

/-- The tree size of a term. -/
def Term.size : Term → ℕ
  | .number _ | .constant _ | .symbol _ => 1
  | .call _ args => 1 + Term.sizeList args
  | .power b _ => 1 + Term.size b
  | .product _ fs => 1 + Term.sizeList fs
  | .sum _ ms => 1 + Term.sizePairs ms
  | .condition _ ops => 1 + Term.sizeList ops
  termination_by structural t => t

/-- The total tree size of a list of terms. -/
def Term.sizeList : List Term → ℕ
  | [] => 0
  | t :: ts => Term.size t + Term.sizeList ts
  termination_by structural ts => ts

/-- The total tree size of the cores of a list of monomials. -/
def Term.sizePairs : List (ℚ × Term) → ℕ
  | [] => 0
  | (_, t) :: ms => Term.size t + Term.sizePairs ms
  termination_by structural ms => ms

end

mutual

/-- The depth of a term. -/
def Term.depth : Term → ℕ
  | .number _ | .constant _ | .symbol _ => 1
  | .call _ args => 1 + Term.depthList args
  | .power b _ => 1 + Term.depth b
  | .product _ fs => 1 + Term.depthList fs
  | .sum _ ms => 1 + Term.depthPairs ms
  | .condition _ ops => 1 + Term.depthList ops
  termination_by structural t => t

/-- The largest depth of a list of terms, 0 for the empty list. -/
def Term.depthList : List Term → ℕ
  | [] => 0
  | t :: ts => max (Term.depth t) (Term.depthList ts)
  termination_by structural ts => ts

/-- The largest depth of the cores of a list of monomials, 0 for none. -/
def Term.depthPairs : List (ℚ × Term) → ℕ
  | [] => 0
  | (_, t) :: ms => max (Term.depth t) (Term.depthPairs ms)
  termination_by structural ms => ms

end

/-- The logical bytes of a rational `n/d`, `|n| + |d| + 3`, where `|x|` is the
bit length of the absolute value: the bytes of a rational in the term formula,
and the storage bytes of a rational in the coefficient fields. -/
def ratBytes (q : ℚ) : ℕ := q.num.natAbs.size + q.den.size + 3

/-- The logical bytes of the kinds whose formula is fixed with them: of a
constant, from the constant; of a call, from its head and the bytes of its
arguments in order; and of a condition, from its shape and the bytes of its
operands in order. -/
structure ByteParams where
  /-- The bytes of a constant. -/
  constant : Constant → ℕ
  /-- The bytes of a call, from its head and the bytes of its arguments. -/
  call : Head → List ℕ → ℕ
  /-- The bytes of a condition, from its shape and the bytes of its operands. -/
  condition : CondShape → List ℕ → ℕ

mutual

/-- The logical bytes of a term (TRM-R08), the term formula of the terms
contract: a number costs the bytes of its value and a symbol the bytes of its
name; a power costs its base, its exponent written as the rational `k/1` and
4 for the operator; a product of `m` factors costs its factors and
`4 (m - 1)` with the coefficient 1, and otherwise its factors, the bytes of
the coefficient and `4 m`; a sum costs its cores, the bytes of each
coefficient other than 1 and 4 more, the bytes of the constant when it is not
0, and 4 for each operator between its parts, its monomials and its constant
when that is not 0. Constants, calls and conditions cost what the parameters
give. A shared subterm counts once for each occurrence. -/
def Term.bytes (p : ByteParams) : Term → ℕ
  | .number q => ratBytes q
  | .constant c => p.constant c
  | .symbol s => s.utf8ByteSize
  | .call h args => p.call h (Term.bytesList p args)
  | .power b k => Term.bytes p b + ratBytes k + 4
  | .product c fs =>
    (Term.bytesList p fs).sum + if c = 1 then 4 * (fs.length - 1) else ratBytes c + 4 * fs.length
  | .sum c ms =>
    Term.bytesPairs p ms + (if c = 0 then 0 else ratBytes c) +
      4 * (ms.length + (if c = 0 then 0 else 1) - 1)
  | .condition s ops => p.condition s (Term.bytesList p ops)
  termination_by structural t => t

/-- The logical bytes of each term of a list, in order. -/
def Term.bytesList (p : ByteParams) : List Term → List ℕ
  | [] => []
  | t :: ts => Term.bytes p t :: Term.bytesList p ts
  termination_by structural ts => ts

/-- The logical bytes of the monomials of a sum: each core, and the bytes of
each coefficient other than 1 and 4 more. -/
def Term.bytesPairs (p : ByteParams) : List (ℚ × Term) → ℕ
  | [] => 0
  | (c, t) :: ms =>
    Term.bytes p t + (if c = 1 then 0 else ratBytes c + 4) + Term.bytesPairs p ms
  termination_by structural ms => ms

end

end Kalyx.Spec.Terms

end
