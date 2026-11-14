module

public import Kalyx.Spec.Terms.Power

/-!
# Terms: calls, classes and symbols

A call `h(args)` is a term of rank 3 (TRM-R14): its head, the name and the
class, and its arguments, canonical terms in their given order, not sorted.
For sums, products and powers a call is an atom (architecture, "Call
nodes"): it can be a base or a core, merges as one with an equal call, and is
never expanded. Its meaning is that of a total uninterpreted function of the
values of its arguments, so the term core treats every call as defined; the
domain of a call is carried by the condition of a function value, which is
not part of this specification.

The call constructor (`mkCall`) checks the class of each argument by its role
(`Head.role`), applies the rule of `piecewise` on a truth value
(`piecewiseBranch`), a rule of the term core, and leaves every other call to
its rules (`RegistryRules`). Those rules are a parameter: the checks and the
rewritings of the call constructor read from the function registry, and the
checks of the order of `derivative` and of the bindings of `substitute`. The
assumptions on them are that they keep the meaning of a call
(`RegistryRules.Keeps`), and that they return canonical values and keep the
bases of negative powers (`RegistryRules.Closed`). The powers of roots and
of `i`, which a root call or the constant `i` triggers, are rules of products
and powers.

Values and conditions are two classes (TRM-R15): the operands of the
connectives and the first argument of `piecewise` are conditions, and every
other operand and argument is a value. An operand of the wrong class fails
with `Syntax` (`Head.argsOk`, `CondShape.takes`).

The symbol constructor (`mkSymbol`) checks the form of a name and rejects the
reserved names (TRM-R11).
-/

@[expose] public section

namespace Kalyx.Spec.Terms

open Kalyx.Spec.Fields (LimitField)

/-! ## Classes and the table of the special forms -/

/-- The role of an argument position of a call. Only a condition position
takes a condition; the other roles take values. The free symbols of a term
skip the variable and the binding positions (architecture, "Call nodes"); how
a binding is written as a term is fixed with the special forms, not here. -/
inductive ArgRole where
  /-- A condition: the first argument of `piecewise`. -/
  | condition
  /-- A value. -/
  | value
  /-- The variable of `derivative`. -/
  | var
  /-- A binding of `substitute`. -/
  | binding
  deriving DecidableEq, Repr

/-- The head of `piecewise(c, a, b)`. -/
def Head.piecewise : Head := ⟨"piecewise", .formal⟩

/-- The head of `derivative(u, x, n)`. -/
def Head.derivative : Head := ⟨"derivative", .formal⟩

/-- The head of `substitute(u, x1 = v1, …)`. -/
def Head.substitute : Head := ⟨"substitute", .formal⟩

/-- The table of the special forms (architecture, "Call nodes"): the role of
the argument at the position `i`, from 0, of a call with the head `h`.
`piecewise(c, a, b)` takes a condition and two values; `derivative(u, x, n)`
a value, the variable and its order, a value; `substitute(u, x1 = v1, …)` a
value and bindings. Every argument of a registered function is a value. The
number of arguments is checked by the rules, not by this table. -/
def Head.role (h : Head) (i : ℕ) : ArgRole :=
  match h.callClass, h.name, i with
  | .formal, "piecewise", 0 => .condition
  | .formal, "derivative", 1 => .var
  | .formal, "substitute", _ + 1 => .binding
  | _, _, _ => .value

/-- Whether the free symbols of a term skip the argument at the position `i`
of a call with the head `h`: the variable and the binding positions. -/
def Head.skips (h : Head) (i : ℕ) : Bool :=
  match h.role i with
  | .var | .binding => true
  | .condition | .value => false

/-- Whether each term of `args`, the arguments from the position `i` on, is of
the class of its role: a condition exactly at a condition position. -/
def Head.argsOkFrom (h : Head) (i : ℕ) : List Term → Bool
  | [] => true
  | t :: ts => (t.isCondition == (h.role i == .condition)) && h.argsOkFrom (i + 1) ts
  termination_by structural ts => ts

/-- Whether the arguments of a call with the head `h` are of their classes. -/
def Head.argsOk (h : Head) (args : List Term) : Bool := h.argsOkFrom 0 args

/-- Whether the shape of a condition takes the operands `ops`, by their number
and their classes (architecture, "Conditions"): a truth value none; a
comparison two values; a property predicate and `defined` one value; `not`
one condition; `and` and `or` two or more conditions. The names of the
properties are not checked. -/
def CondShape.takes : CondShape → List Term → Bool
  | .truth _, ops => ops.isEmpty
  | .comparison _, ops => ops.length == 2 && ops.all (!·.isCondition)
  | .predicate _, ops | .defined, ops => ops.length == 1 && ops.all (!·.isCondition)
  | .not, ops => ops.length == 1 && ops.all (·.isCondition)
  | .and, ops | .or, ops => decide (2 ≤ ops.length) && ops.all (·.isCondition)

/-! ## The rules of calls -/

/-- What the rules do with a call: keep the node, rewrite it into a term, or
fail with a fault or with `ResourceLimit` naming a field of the limits. -/
inductive RuleOutcome where
  /-- The call stays a node. -/
  | keep
  /-- The call is the term `t`. -/
  | rewrite (t : Term)
  /-- The call fails with the fault `kind`. -/
  | fault (kind : TermFault)
  /-- The call fails with `ResourceLimit` naming `field`. -/
  | resourceLimit (field : LimitField)
  deriving DecidableEq

/-- The rules of calls, a parameter of this specification (TRM-R14): for the
limit `maxExponent`, a head and canonical arguments of their classes, what the
call constructor does with the call. Of kalyx's call constructor
(architecture, "Rules of the call constructor") they hold the lookup of the
name and the number of arguments (`Syntax`), the degree of `rootn` and its
two rules, the domains on the listed arguments, parity, the point values, the
quarter turns, the principal roots of rationals and the absolute values; of
the special forms, the checks of the order of `derivative` and of the
bindings of `substitute`. The rules of the term core that a head or a
constant triggers are not among them. -/
structure RegistryRules where
  /-- The outcome for the limit `maxExponent`, the head and the arguments. -/
  apply : ℕ → Head → List Term → RuleOutcome

/-- The rules that keep every call, which apply no rule of the registry: the
rules of the replays and of the examples. -/
def RegistryRules.empty : RegistryRules := ⟨fun _ _ _ => .keep⟩

/-- The rules keep what `f` gives: a call that they rewrite and its result have
the same image. With the meaning of a term at an assignment as `f`, at every
assignment, this is the soundness of the rules, each rewrite an identity with
the same domain on both sides (architecture, "Rules of the call
constructor"). Faults are not covered: the semantics of a call is total. -/
def RegistryRules.Keeps {V : Type} (R : RegistryRules) (f : Term → V) : Prop :=
  ∀ maxExponent h args t, R.apply maxExponent h args = .rewrite t → f t = f (.call h args)

/-- The rules are closed for the canonical forms `canonical` and keep the bases
`bases`: on canonical arguments, the result of a rewrite is a canonical value
that holds every base that the call holds. With the canonical-form predicate
and the bases of `N`, a rewrite returns a canonical term and drops no point
where its input is undefined. -/
def RegistryRules.Closed {β : Type} [Membership Term β] (R : RegistryRules)
    (canonical : Term → Prop) (bases : Term → β) : Prop :=
  ∀ maxExponent h args t, (∀ a ∈ args, canonical a) → R.apply maxExponent h args = .rewrite t →
    canonical t ∧ t.isCondition = false ∧ ∀ b ∈ bases (.call h args), b ∈ bases t

/-- The rule of `piecewise`, a rule of the term core (architecture, "Rules of
the call constructor"): on the arguments `true, a, b` the term `a`, on
`false, a, b` the term `b`, and none on any other arguments. -/
def piecewiseBranch : List Term → Option Term
  | [.condition (.truth c) [], a, b] => some (if c then a else b)
  | _ => none

/-- The call constructor (TRM-R14), on canonical arguments: an argument of the
wrong class fails with `Syntax`; `piecewise` on a truth value is the branch
that it selects; every other call is what the rules give, the node itself
when they keep it. -/
def mkCall (maxExponent : ℕ) (R : RegistryRules) (h : Head) (args : List Term) : Result Term :=
  if !h.argsOk args then .fault (.syntax none)
  else
    match (if h = .piecewise then piecewiseBranch args else none) with
    | some t => .value t
    | none =>
      match R.apply maxExponent h args with
      | .keep => .value (.call h args)
      | .rewrite t => .value t
      | .fault k => .fault k
      | .resourceLimit f => .resourceLimit f

/-! ## Symbols -/

/-- The names reserved for the constants and for the branch of `piecewise`
that has no value: `pi`, `i` and `undefined`. -/
def reservedNames : List String := ["pi", "i", "undefined"]

/-- The span of the first character of `cs` that the form of a symbol name does
not allow, where `cs` starts at the byte `pos` of the name and `first` marks
the first character of the name: an ASCII letter or `_` first, then ASCII
letters, digits and `_`. The span covers the whole character, also when it is
not ASCII. -/
def nameFaultFrom (first : Bool) (pos : ℕ) : List Char → Option Span
  | [] => none
  | c :: cs =>
    if c.isAlpha || c == '_' || (!first && c.isDigit) then nameFaultFrom false (pos + c.utf8Size) cs
    else some ⟨pos, pos + c.utf8Size⟩
  termination_by structural cs => cs

/-- The span of the fault of a symbol name (terms contract, "Symbol names"):
the empty span at 0 for the empty name, the span of the first character that
the form does not allow, or none for a name of the right form. -/
def nameFault (name : String) : Option Span :=
  match name.toList with
  | [] => some ⟨0, 0⟩
  | cs => nameFaultFrom true 0 cs

/-- The symbol constructor, `Term::symbol` (TRM-R11): a name of the wrong form
fails with `Syntax` and the span of `nameFault`; then a reserved name fails
with `Unsupported` and the span of the whole name; any other name is the
symbol. -/
def mkSymbol (name : String) : Result Term :=
  match nameFault name with
  | some span => .fault (.syntax (some span))
  | none =>
    if name ∈ reservedNames then .fault (.unsupported (some ⟨0, name.utf8ByteSize⟩))
    else .value (.symbol name)

end Kalyx.Spec.Terms

end
