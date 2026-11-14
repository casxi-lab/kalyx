module

public import Kalyx.Spec.Terms.Term

/-!
# Terms: the total order

`Term.cmp o` is the total order of terms (TRM-R03), a pure function: by rank
first, and within a rank by the rules of the terms contract ("Kinds and the
total order") and of the architecture ("Kinds and order", "Order and cache").
The orders that the design does not fix down to single values are parameters
(`Orders`), of which the statements assume only that they are total
(`Orders.Total`); `Orders.sample` is one choice of them for replays and
examples, not kalyx's.

The order is the ordering of the first difference that a walk of two terms
finds (`Term.firstDifference`), as kalyx's comparison stops at the first pair
of parts that differs. Of its steps, only the comparison of two rationals can
fail under the limits of this specification, when it forms their cross
products (numbers contract, "Comparison"). So `Term.compareAt`, the
comparison under an explicit `maxIntegerBits` (TRM-R08), is the order unless
the first difference is a pair of rationals, and `ratCompareAt` on that pair
otherwise; equal terms compare `eq` under every limit.

Factors are sorted by their keys (`Key`) and monomials by their cores, by
insertion; adjacent items merge (`sortBy`, `mergeAdjacent`). Both recurse
structurally.
-/

@[expose] public section

namespace Kalyx.Spec.Terms

/-! ## Orders of the parts -/

/-- The lexicographic order of two lists by `c`: the first position that
differs decides, and a proper prefix comes first. -/
def lexCmp {α : Type} (c : α → α → Ordering) : List α → List α → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (c a b).then (lexCmp c as bs)
  termination_by structural as _ => as

/-- The order of names by their UTF-8 bytes, a proper prefix first: `x`
before `xy`, `B` before `a`, and `i` before `pi`. -/
def nameCmp (a b : String) : Ordering :=
  lexCmp (fun x y => compare x.toNat y.toNat) a.toByteArray.data.toList b.toByteArray.data.toList

/-- The order of rationals by value. -/
def ratCmp (a b : ℚ) : Ordering := if a < b then .lt else if a = b then .eq else .gt

/-- The order of the classes of calls: `Registered` before `Formal`. -/
def CallClass.cmp : CallClass → CallClass → Ordering
  | .registered, .formal => .lt
  | .formal, .registered => .gt
  | _, _ => .eq

/-- `c` is a total order: oriented, so that `c b a` is the swap of `c a b`;
transitive; and `eq` only for equal arguments (`Std.TransCmp` and
`Std.LawfulEqCmp`). -/
def TotalCmp {α : Type} (c : α → α → Ordering) : Prop := Std.TransCmp c ∧ Std.LawfulEqCmp c

/-- The shape of a condition without its relation or its property: each
truth value is a shape of its own. -/
inductive CondKind where
  | truth (value : Bool)
  | comparison | predicate | defined | not | and | or
  deriving DecidableEq, Repr

/-- The shape of a condition without its relation or its property. -/
def CondShape.kind : CondShape → CondKind
  | .truth b => .truth b
  | .comparison _ => .comparison
  | .predicate _ => .predicate
  | .defined => .defined
  | .not => .not
  | .and => .and
  | .or => .or

/-- The orders that the design does not fix down to single values, the
parameters of the order of terms. The architecture orders conditions within
rank 7 by shape first, then by the relation or the property, then by their
operands, without ordering the shapes, the relations or the properties among
themselves: `shapes`, `relations` and `properties` give these three orders.
`coefficients` orders the coefficient lists of the minimal polynomials of two
algebraic constants of one type and one degree, between the degree and the
index: the architecture orders them "by the coefficients of `m`". -/
structure Orders where
  /-- The order of the shapes of conditions. -/
  shapes : CondKind → CondKind → Ordering
  /-- The order of the relations of comparisons. -/
  relations : Relation → Relation → Ordering
  /-- The order of the properties of property predicates, by their names. -/
  properties : String → String → Ordering
  /-- The order of the coefficient lists of minimal polynomials of one
  degree. -/
  coefficients : List ℚ → List ℚ → Ordering

/-- The orders of the parameters are total. -/
def Orders.Total (o : Orders) : Prop :=
  TotalCmp o.shapes ∧ TotalCmp o.relations ∧ TotalCmp o.properties ∧ TotalCmp o.coefficients

/-- The order of the shapes of conditions with their relations and
properties: by shape, then the relations of two comparisons, or the
properties of two property predicates. -/
def CondShape.cmp (o : Orders) (s r : CondShape) : Ordering :=
  (o.shapes s.kind r.kind).then
    (match s, r with
      | .comparison a, .comparison b => o.relations a b
      | .predicate p, .predicate q => o.properties p q
      | _, _ => .eq)

/-- The order of the identities of two algebraic constants of one type: by
degree, the length of the list of `m`, then by the coefficients of `m` in the
order of the parameters, then by the index. -/
def AlgebraicId.cmp (o : Orders) (x y : AlgebraicId) : Ordering :=
  (compare x.minimal.length y.minimal.length).then
    ((o.coefficients x.minimal y.minimal).then (compare x.index y.index))

/-- The order of constants (TRM-R13): the named constants first, by the bytes
of their names, so `i` comes before `π`; then the algebraic constants, real
before complex, and within each type by `AlgebraicId.cmp`. -/
def Constant.cmp (o : Orders) : Constant → Constant → Ordering
  | .named a, .named b => nameCmp a.name b.name
  | .named _, _ => .lt
  | _, .named _ => .gt
  | .real x, .real y => x.cmp o y
  | .real _, .complex _ => .lt
  | .complex _, .real _ => .gt
  | .complex x, .complex y => x.cmp o y

/-! ## The order of terms -/

/-- What the walk of two terms finds first. -/
inductive Difference where
  /-- No difference: the terms are equal. -/
  | equal
  /-- Two different rationals, `a` of the first term and `b` of the second:
  two numbers, two coefficients of products, two coefficients of monomials
  or two constants of sums. -/
  | rationals (a b : ℚ)
  /-- Two other parts that differ, the first `r`, `lt` or `gt`, of the second:
  ranks, constants, names, classes, exponents, shapes of conditions, or the
  numbers of children. -/
  | other (r : Ordering)
  deriving DecidableEq, Repr

/-- The difference that the ordering of two parts gives: none for `eq`. -/
def Difference.ofOrdering : Ordering → Difference
  | .eq => .equal
  | r => .other r

/-- The difference of two rationals: none when they are equal. -/
def Difference.ofRationals (a b : ℚ) : Difference :=
  if a = b then .equal else .rationals a b

/-- The difference of two pairs of parts compared in order: that of the first
pair, or that of the second when the first parts are equal. -/
def Difference.andThen : Difference → Difference → Difference
  | .equal, d => d
  | d, _ => d

/-- The ordering that a difference decides: `eq` for none, and for two
rationals their order by value. -/
def Difference.order : Difference → Ordering
  | .equal => .eq
  | .rationals a b => ratCmp a b
  | .other r => r

mutual

/-- The first difference that the walk of two terms finds. Terms of different
ranks differ in their ranks. Within a rank: numbers by value; constants by
`Constant.cmp`; symbols by the bytes of their names; calls by the bytes of the
head name, then the class, then the arguments; powers by base, then
exponent; products by their factors, then the coefficient; sums by their
monomials, each by its core and then its coefficient, then the constant;
conditions by their shape and then their relation or property, in the orders
of the parameters (`CondShape.cmp`), then their operands. Children are compared one by one over the common positions, and
then by their numbers, so that a proper prefix comes first. -/
def Term.firstDifference (o : Orders) : Term → Term → Difference
  | .number a, .number b => .ofRationals a b
  | .constant c, .constant d => .ofOrdering (Constant.cmp o c d)
  | .symbol a, .symbol b => .ofOrdering (nameCmp a b)
  | .call h as, .call g bs =>
    (Difference.ofOrdering ((nameCmp h.name g.name).then (h.callClass.cmp g.callClass))).andThen
      (Term.firstDifferenceList o as bs)
  | .power b k, .power c l => (Term.firstDifference o b c).andThen (.ofOrdering (compare k l))
  | .product a fs, .product b gs => (Term.firstDifferenceList o fs gs).andThen (.ofRationals a b)
  | .sum a ms, .sum b ns => (Term.firstDifferencePairs o ms ns).andThen (.ofRationals a b)
  | .condition s xs, .condition r ys =>
    (Difference.ofOrdering (CondShape.cmp o s r)).andThen (Term.firstDifferenceList o xs ys)
  | t, u => .ofOrdering (compare t.rank u.rank)
  termination_by structural t _ => t

/-- The first difference of two lists of terms. -/
def Term.firstDifferenceList (o : Orders) : List Term → List Term → Difference
  | [], [] => .equal
  | [], _ :: _ => .other .lt
  | _ :: _, [] => .other .gt
  | t :: ts, u :: us => (Term.firstDifference o t u).andThen (Term.firstDifferenceList o ts us)
  termination_by structural ts _ => ts

/-- The first difference of two lists of monomials, each compared by its
core and then its coefficient. -/
def Term.firstDifferencePairs (o : Orders) : List (ℚ × Term) → List (ℚ × Term) → Difference
  | [], [] => .equal
  | [], _ :: _ => .other .lt
  | _ :: _, [] => .other .gt
  | (a, t) :: ms, (b, u) :: ns =>
    ((Term.firstDifference o t u).andThen (.ofRationals a b)).andThen
      (Term.firstDifferencePairs o ms ns)
  termination_by structural ms _ => ms

end

/-- The total order of terms under the parameters `o`: the ordering of the
first difference of the walk. kalyx's `equals` is this order giving `eq`. -/
def Term.cmp (o : Orders) (s t : Term) : Ordering := (Term.firstDifference o s t).order

/-! ## Keys of factors -/

/-- The key of a factor of a product (terms contract, "Products"; architecture,
"Constants"): its base, and whether its exponent counts as negative. Items
`b ^ k` of one key merge by adding their exponents, so over a base that is
not a constant, exponents of opposite signs never merge; over a constant
base, whose exponents of both signs merge, the sign is not part of the
key. -/
structure Key where
  /-- The base. -/
  base : Term
  /-- The exponent is negative and the base is not a constant. -/
  negative : Bool
  deriving DecidableEq

/-- The key of the item `b ^ k`. -/
def Key.of (b : Term) (k : ℤ) : Key := ⟨b, decide (k < 0) && !b.isConstant⟩

/-- The key of a factor: of a power `b ^ k`, that of the item `(b, k)`; of
any other factor `t`, that of `(t, 1)`. So a one `(b⁻¹)⁰` has the key of its
base `b⁻¹` with a nonnegative exponent. -/
def Term.key : Term → Key
  | .power b k => Key.of b k
  | t => Key.of t 1

/-- The order of keys: by base in the order of terms, and for one base the
key with a nonnegative exponent first. -/
def Key.cmp (o : Orders) (x y : Key) : Ordering :=
  (Term.cmp o x.base y.base).then (compare x.negative.toNat y.negative.toNat)

/-! ## Comparison under `max_integer_bits` -/

/-- The bound on the bits of the cross products `a d` and `c b` of two
rationals `a/b` and `c/d`, `max (|a| + |d|) (|c| + |b|)`, where `|x|` is the
bit length of the absolute value (numbers contract, "Checks and charges"). -/
def ratCrossBound (x y : ℚ) : ℕ :=
  max (x.num.natAbs.size + y.den.size) (y.num.natAbs.size + x.den.size)

/-- Whether a natural number is a power of two. -/
def isPowerOfTwo (n : ℕ) : Bool := n == 2 ^ (n.size - 1)

/-- Whether kalyx's comparison of two rationals `a/b` and `c/d` forms their
cross products (numbers contract, "Comparison"): it takes the first of these
paths that applies, equal parts, different signs, two denominators that are
powers of two, equal denominators, and sums of bit lengths `|a| + |d|` and
`|c| + |b|` that differ by at least two, and forms the cross products when
none applies. -/
def ratNeedsCross (x y : ℚ) : Bool :=
  let s := x.num.natAbs.size + y.den.size
  let t := y.num.natAbs.size + x.den.size
  x != y && x.num.sign == y.num.sign && !(isPowerOfTwo x.den && isPowerOfTwo y.den) &&
    x.den != y.den && s < t + 2 && t < s + 2

/-- The comparison of two rationals under `maxIntegerBits`: `ResourceLimit`
naming `max_integer_bits` when it forms the cross products and their bound is
above the limit, and otherwise their order by value. Equal rationals compare
`eq` under every limit. -/
def ratCompareAt (maxIntegerBits : ℕ) (x y : ℚ) : Result Ordering :=
  if ratNeedsCross x y && maxIntegerBits < ratCrossBound x y then .resourceLimit .integerBits
  else .value (ratCmp x y)

/-- The comparison of two terms under `maxIntegerBits`, kalyx's `compare` of a
term with the checks of its numbers against the receiving limits (terms
contract, "Size, depth and storage"): where the first difference of the walk
is a pair of rationals, their comparison under the limit, and otherwise the
order of terms. -/
def Term.compareAt (o : Orders) (maxIntegerBits : ℕ) (s t : Term) : Result Ordering :=
  match Term.firstDifference o s t with
  | .rationals a b => ratCompareAt maxIntegerBits a b
  | d => .value d.order

/-- kalyx's `equals` under `maxIntegerBits`: the comparison giving `eq`. -/
def Term.equalsAt (o : Orders) (maxIntegerBits : ℕ) (s t : Term) : Result Bool :=
  (Term.compareAt o maxIntegerBits s t).map (· == .eq)

/-! ## Sorting and merging -/

/-- `x` inserted into a list before its first element that `x` is not above
in the order `c`. -/
def insertBy {α : Type} (c : α → α → Ordering) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if c x y == .gt then y :: insertBy c x ys else x :: y :: ys
  termination_by structural ys => ys

/-- A list sorted in the order `c` by insertion; of two elements that compare
`eq`, the earlier comes first. -/
def sortBy {α : Type} (c : α → α → Ordering) : List α → List α
  | [] => []
  | x :: xs => insertBy c x (sortBy c xs)
  termination_by structural xs => xs

/-- A list with adjacent elements joined, from the right: `join x y` is
`some z` when the adjacent elements `x` and `y` merge into `z`, and `none`
when they stay apart. -/
def mergeAdjacent {α : Type} (join : α → α → Option α) : List α → List α
  | [] => []
  | x :: rest =>
    match mergeAdjacent join rest with
    | y :: more =>
      match join x y with
      | some z => z :: more
      | none => x :: y :: more
    | [] => [x]
  termination_by structural xs => xs

/-- Whether each element of a list is below the next in the order `c`, so that
the list increases strictly. -/
def strictlyIncreasing {α : Type} (c : α → α → Ordering) : List α → Bool
  | [] => true
  | x :: rest =>
    (match rest with
      | y :: _ => c x y == .lt
      | [] => true) && strictlyIncreasing c rest
  termination_by structural xs => xs

/-! ## A choice of the parameters -/

/-- A sample order of the shapes of conditions: `false`, `true`, the
comparisons, the predicates, `defined`, `not`, `and`, `or`. -/
def CondKind.sampleCmp (s r : CondKind) : Ordering :=
  let index : CondKind → ℕ
    | .truth false => 0 | .truth true => 1 | .comparison => 2 | .predicate => 3
    | .defined => 4 | .not => 5 | .and => 6 | .or => 7
  compare (index s) (index r)

/-- A sample order of the relations: `==`, `!=`, `<`, `<=`, `>`, `>=`. -/
def Relation.sampleCmp (a b : Relation) : Ordering :=
  let index : Relation → ℕ
    | .eq => 0 | .ne => 1 | .lt => 2 | .le => 3 | .gt => 4 | .ge => 5
  compare (index a) (index b)

/-- A choice of the parameters for replays and examples, not kalyx's orders:
the sample orders of the shapes and of the relations, the properties by the
bytes of their names, and coefficient lists lexicographically by value from
the constant term. -/
def Orders.sample : Orders := ⟨CondKind.sampleCmp, Relation.sampleCmp, nameCmp, lexCmp ratCmp⟩

end Kalyx.Spec.Terms

end
