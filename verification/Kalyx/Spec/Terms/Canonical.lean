module

public import Kalyx.Spec.Terms.Algebraic

/-!
# Terms: the canonical form

The canonical-form predicate (TRM-R02) says which trees are the terms that the
constructors return: every node has the canonical shape of the terms contract
("Canonical shape"), with what the constants, calls and conditions add
(architecture, "Constants", "Call nodes", "Rules of the call constructor",
"Conditions", "Algebraic numbers as terms"):

* no power has the base `i`, and a constant gives at most one factor of a
  product, since its key does not hold the sign of its exponent;
* a power of a root of a literal degree `n` has an exponent below `n`;
* a call is of the classes of its positions, `piecewise` does not hold a
  truth value as its condition, and the rules of calls keep it;
* an algebraic constant holds an identity that no closed form covers, and a
  valid one;
* a condition stands only where a condition is taken, and has the number and
  the classes of operands of its shape.

The predicate reads what the constructors read: the order of terms `o`, by
which factors and monomials are sorted, and the rules of calls `R` under the
limit `maxExponent`, which decide the calls that are kept. It has two parts:
the shape (`Term.shapeOk`), decided node by node (`Term.nodeOk`), and the
validity of the identities of algebraic constants (`Term.ConstantsValid`), a
proposition, since irreducibility and the positions of roots are not decided
here.

Rebuilding a canonical term through the constructors from its parts, as the
accessors give them, gives the term (terms contract, "Idempotence";
`Term.rebuild`), where the limit admits its exponents
(`Term.exponentsWithin`).
-/

@[expose] public section

namespace Kalyx.Spec.Terms

/-! ## Nodes -/

mutual

/-- The nodes of a term: the term itself, then the nodes of its children in
order, a shared subterm once for each occurrence. -/
def Term.nodes : Term → List Term
  | .number q => [.number q]
  | .constant c => [.constant c]
  | .symbol s => [.symbol s]
  | .call h args => .call h args :: Term.nodesList args
  | .power b k => .power b k :: Term.nodes b
  | .product c fs => .product c fs :: Term.nodesList fs
  | .sum c ms => .sum c ms :: Term.nodesPairs ms
  | .condition s ops => .condition s ops :: Term.nodesList ops
  termination_by structural t => t

/-- The nodes of the terms of a list, in order. -/
def Term.nodesList : List Term → List Term
  | [] => []
  | t :: ts => Term.nodes t ++ Term.nodesList ts
  termination_by structural ts => ts

/-- The nodes of the cores of a list of monomials, in order. -/
def Term.nodesPairs : List (ℚ × Term) → List Term
  | [] => []
  | (_, t) :: ms => Term.nodes t ++ Term.nodesPairs ms
  termination_by structural ms => ms

end

/-! ## Powers and products -/

/-- Whether a term can be a factor of a product or the base of a power: a
value that is neither a number nor a product, and a sum only when it is
primitive, its content 1. -/
def Term.factorOk : Term → Bool
  | .number _ | .product .. | .condition .. => false
  | .sum c ms => sumContent c ms == 1
  | _ => true

/-- The shape of a power node `b ^ k`: `b` can be a factor and is not `i`; the
exponent is not 1; it is 0 only in a one `(c⁻¹)⁰` over a base `c` that is
not a constant; when `b` is a power `cʲ`, the merge condition does not hold
for `j` and `k`; and when `b` is a root of the literal degree `n`, `k < n`. -/
def canonicalPower (b : Term) (k : ℤ) : Bool :=
  b.factorOk && b != Term.imaginaryUnit && k != 1 &&
    (match rootOf b with
      | some (_, n) => decide (k < (n : ℤ))
      | none => true) &&
    match b with
    | .power c j => !mergeCondition j k && (k != 0 || (j == -1 && !c.isConstant))
    | _ => k != 0

/-- The base `b` of a reciprocal `b⁻¹` whose base is not a constant; none for
any other term. -/
def Term.reciprocalBase? : Term → Option Term
  | .power b (-1) => if b.isConstant then none else some b
  | _ => none

/-- The base `b` of a one `(b⁻¹)⁰`; none for any other term. -/
def Term.oneBase? : Term → Option Term
  | .power (.power b (-1)) 0 => some b
  | _ => none

/-- Whether no base of `bs` occurs with a negative exponent inside a base of
`bs`, so that the bases are their own maximal elements (`maxBases`). -/
def unnested (bs : List Term) : Bool := bs.all fun b => !bs.any fun c => c.negBases.contains b

/-- The shape of a product node `c · fs`: at least one factor, and a single
factor only with a coefficient other than 1 and only when that factor is not
a sum; every factor can be a factor; and the keys of the factors increase
strictly (`Key.cmp`), so a constant gives at most one factor. With the
coefficient 0, every factor is a reciprocal `b⁻¹` over a base that is not a
constant, and no base occurs with a negative exponent inside another. With
another coefficient, no factor other than a one holds the base of a one with
a negative exponent, and no base of a one occurs with a negative exponent
inside the base of another one. -/
def canonicalProduct (o : Orders) (c : ℚ) (fs : List Term) : Bool :=
  fs.all Term.factorOk && strictlyIncreasing (Key.cmp o) (fs.map Term.key) &&
    (match fs with
      | [] => false
      | [f] => c != 1 && !(f matches .sum ..)
      | _ => true) &&
    if c = 0 then
      match fs.mapM Term.reciprocalBase? with
      | some bs => unnested bs
      | none => false
    else
      let bs := fs.filterMap Term.oneBase?
      let held := Term.negBasesList (fs.filter fun f => !f.isOne)
      unnested bs && bs.all fun b => !held.contains b

/-! ## Sums -/

/-- Whether a term can be the core of a monomial: a value that is neither a
number nor a sum, and a product only with the coefficient 1. -/
def Term.coreOk : Term → Bool
  | .number _ | .sum .. | .condition .. => false
  | .product a _ => a == 1
  | _ => true

/-- The bases of the core of a witness monomial: `b` for a reciprocal `b⁻¹`,
and the bases of a product of reciprocals with the coefficient 1, none of
them a constant; none for any other core. -/
def witnessBases? : Term → Option (List Term)
  | .product a fs => if a = 1 then fs.mapM Term.reciprocalBase? else none
  | t => t.reciprocalBase?.map ([·])

/-- The shape of a sum node of the constant `c` and the monomials `ms`: at
least two parts, its monomials and its constant when that is not 0; every
core can be a core; the cores increase strictly in the order of terms; and
at most one monomial has the coefficient 0, the witness monomial, whose core
is a reciprocal or a product of reciprocals with the coefficient 1 over bases
that no other core holds with a negative exponent and that do not occur with
a negative exponent inside one another. -/
def canonicalSum (o : Orders) (c : ℚ) (ms : List (ℚ × Term)) : Bool :=
  decide (2 ≤ ms.length + (if c = 0 then 0 else 1)) && ms.all (fun m => m.2.coreOk) &&
    strictlyIncreasing (Term.cmp o) (ms.map Prod.snd) &&
    match ms.filter fun m => decide (m.1 = 0) with
    | [] => true
    | [(_, w)] =>
      match witnessBases? w with
      | some bs =>
        let held := Term.negBasesPairs (ms.filter fun m => decide (m.1 ≠ 0))
        unnested bs && bs.all fun b => !held.contains b
      | none => false
    | _ => false

/-! ## Calls and the canonical form -/

/-- The shape of a call node `h(args)` under the rules `R` and the limit
`maxExponent`: each argument is of the class of its position, `piecewise`
does not hold a truth value as its condition, and the rules keep the call. -/
def canonicalCall (maxExponent : ℕ) (R : RegistryRules) (h : Head) (args : List Term) : Bool :=
  h.argsOk args && (h != .piecewise || (piecewiseBranch args).isNone) &&
    R.apply maxExponent h args == .keep

/-- The shape of the node at the root of a term, its children aside: any
number, whose rational is reduced by construction; a constant that no closed
form covers (`Constant.hasClosedForm`); a symbol whose name has the form of a
name and is not reserved; a call, a power, a product and a sum as above; and a
condition whose operands are of the number and the classes of its shape. -/
def Term.nodeOk (o : Orders) (maxExponent : ℕ) (R : RegistryRules) : Term → Bool
  | .number _ => true
  | .constant c => !c.hasClosedForm
  | .symbol s => (nameFault s).isNone && !reservedNames.contains s
  | .call h args => canonicalCall maxExponent R h args
  | .power b k => canonicalPower b k
  | .product c fs => canonicalProduct o c fs
  | .sum c ms => canonicalSum o c ms
  | .condition s ops => s.takes ops

/-- The shape part of the canonical form: every node has its canonical
shape. -/
def Term.shapeOk (o : Orders) (maxExponent : ℕ) (R : RegistryRules) (t : Term) : Bool :=
  t.nodes.all (Term.nodeOk o maxExponent R)

/-- Every constant of the term is valid (`Constant.Valid`): the identity of
each algebraic constant names a root of a monic irreducible polynomial of
degree at least 2. -/
def Term.ConstantsValid (t : Term) : Prop := ∀ c, Term.constant c ∈ t.nodes → c.Valid

/-- The canonical form of a term (TRM-R02) under the order `o`, the limit
`maxExponent` and the rules of calls `R`: its shape, decided, and the
validity of its constants. -/
def Term.Canonical (o : Orders) (maxExponent : ℕ) (R : RegistryRules) (t : Term) : Prop :=
  t.shapeOk o maxExponent R = true ∧ t.ConstantsValid

/-! ## Rebuilding -/

/-- `maxExponent` admits the exponents of a term: no power of the term has an
exponent whose magnitude is above the effective bound (`exponentBound`). -/
def Term.exponentsWithin (maxExponent : ℕ) (t : Term) : Bool :=
  t.nodes.all fun u => match u with
    | .power _ k => decide (k.natAbs ≤ exponentBound maxExponent)
    | _ => true

/-- A term rebuilt through the constructors from its parts, as the accessors
give them, the parts taken as they are (terms contract, "Idempotence"): a
number is itself; a constant is the term of its number (`Constant.embed`); a
symbol, a call, a power and a product are built by `mkSymbol`, `mkCall`,
`mkPower` and `mkProduct` from the name, the head and the arguments, the base
and the exponent, and the coefficient and the factors; a sum by `mkSum` from
its constant and its monomials, each the product (`mkProduct`) of its
coefficient and its core; and a condition by the constructor of conditions,
which checks the number and the classes of its operands. -/
def Term.rebuild (o : Orders) (maxExponent : ℕ) (R : RegistryRules) : Term → Result Term
  | .number q => .value (.number q)
  | .constant c => .value c.embed
  | .symbol s => mkSymbol s
  | .call h args => mkCall maxExponent R h args
  | .power b k => mkPower o maxExponent b k
  | .product c fs => mkProduct o maxExponent (.number c :: fs)
  | .sum c ms => do
    let ts ← ms.mapM fun m => mkProduct o maxExponent [.number m.1, m.2]
    mkSum o (.number c :: ts)
  | .condition s ops => if s.takes ops then .value (.condition s ops) else .fault (.syntax none)

end Kalyx.Spec.Terms

end
