module

public import Mathlib.Data.Nat.Notation

/-!
# Coefficient fields: the shared notions

The specification of the coefficient fields of kalyx (the coefficient-field
trait, the rationals, the integers, the residue rings, the prime fields, the
number fields and the maps between them) is written from the numbered
requirements of the numbers contract (`docs/components/numbers/contract.md`),
not from the implementation. This module holds the notions that all its parts
share:

* `ZeroTest`, the answer of a zero test, and `ZeroTest.Sound`, what makes an
  answer reliable;
* `Canonical`, a representation of the elements of a structure of Mathlib by
  the representatives that the library stores, with the canonical ones among
  them, and the two properties that make canonical forms unique and complete;
* `Outcome`, the result of an operation: a value, a fault of a kind that the
  coefficient fields report (`FieldError`), or `ResourceLimit` naming a field
  of the limits (`LimitField`);
* the checks of the limits. The limits that an operation reads are explicit
  parameters, such as `maxIntegerBits` and `maxExponent`, not a request
  context. The checks state where an operation may report `ResourceLimit`;
  they are statements only, not the object of a refinement. Work charges,
  cancellation and deadlines are not part of this specification.
-/

@[expose] public section

namespace Kalyx.Spec.Fields

/-! ## Zero tests -/

/-- The answer of a zero test, as the trait's `ZeroTest<U>`: the element is
zero, it is nonzero, or the test is undecided for a reason of type `U`. A
structure whose zero test always decides has a reason type without values,
`Empty`. -/
inductive ZeroTest (U : Type) where
  /-- The element is zero. -/
  | zero
  /-- The element is not zero. -/
  | nonzero
  /-- The test does not decide, for the given reason. -/
  | undecided (reason : U)
  deriving DecidableEq, Repr

/-- The answer `t` is sound for the proposition `P` that the element is zero:
`zero` only when `P` holds and `nonzero` only when it does not. An undecided
answer carries no information. -/
def ZeroTest.Sound {U : Type} (t : ZeroTest U) (P : Prop) : Prop :=
  (t = .zero → P) ∧ (t = .nonzero → ¬P)

/-- The answer of a decidable test: `zero` when `P` holds and `nonzero`
otherwise, never undecided. -/
def ZeroTest.ofDecide {U : Type} (P : Prop) [Decidable P] : ZeroTest U :=
  if P then .zero else .nonzero

/-! ## Canonical representations -/

/-- A representation of the elements of `K`, a structure of Mathlib, by
representatives of type `R`, the values that the library stores: the element
that each representative denotes, and which representatives are canonical.
Unlike the representatives, the canonical forms are what the operations
return. -/
structure Canonical (R K : Type) where
  /-- The element of `K` that a representative denotes. -/
  interpret : R → K
  /-- The canonical representatives. -/
  canonical : R → Prop

/-- Canonical forms are unique: two canonical representatives that denote the
same element are equal, so the interpretation is injective on them. -/
def Canonical.Unique {R K : Type} (c : Canonical R K) : Prop :=
  ∀ r s, c.canonical r → c.canonical s → c.interpret r = c.interpret s → r = s

/-- Canonical forms are complete: every element of `K` has a canonical
representative. -/
def Canonical.Complete {R K : Type} (c : Canonical R K) : Prop :=
  ∀ x, ∃ r, c.canonical r ∧ c.interpret r = x

/-! ## Outcomes -/

/-- The faults that the operations of the coefficient fields report, a part of
the fault kinds of kalyx: a zero divisor, the inverse of zero or a negative
power of zero (`DivisionByZero`); an argument outside the domain of the
operation, such as a modulus that is not positive or a residue at or above its
modulus (`OutsideDomain`); and values of two different parent structures
(`VariableMismatch`). -/
inductive FieldError where
  /-- `DivisionByZero`. -/
  | divisionByZero
  /-- `OutsideDomain`. -/
  | outsideDomain
  /-- `VariableMismatch`. -/
  | variableMismatch
  deriving DecidableEq, Repr

/-- The fields of the limits of a request, as kalyx's `LimitField`, in the
order of `Limits`. The coefficient fields check `integerBits` and
`exponent`. -/
inductive LimitField where
  /-- `max_work`: the work units charged by the request. -/
  | work
  /-- `max_input_bytes`: the bytes of the input of the request. -/
  | inputBytes
  /-- `max_output_bytes`: the bytes of all display and serialization. -/
  | outputBytes
  /-- `max_depth`: the nesting depth of syntax, terms and values. -/
  | depth
  /-- `max_nodes`: the nodes retained at one time. -/
  | nodes
  /-- `max_storage_bytes`: the logical storage bytes retained at one time. -/
  | storageBytes
  /-- `max_integer_bits`: the bits of one integer. -/
  | integerBits
  /-- `max_exponent`: the absolute value of one integer exponent. -/
  | exponent
  /-- `max_frames`: the frames open at one time. -/
  | frames
  deriving DecidableEq, Repr

/-- The outcome of an operation: a value, a fault, or `ResourceLimit` naming the
field of the limits that a check found exceeded. The failures of a request
context (cancellation, an expired deadline, exhausted work) are not
outcomes of this specification. -/
inductive Outcome (α : Type) where
  /-- The operation returns the value `v`. -/
  | value (v : α)
  /-- The operation fails with the fault `kind`. -/
  | fault (kind : FieldError)
  /-- The operation fails with `ResourceLimit` naming `field`. -/
  | resourceLimit (field : LimitField)
  deriving DecidableEq, Repr

/-- The outcome with `f` applied to its value; faults and limits are kept. -/
def Outcome.map {α β : Type} (f : α → β) : Outcome α → Outcome β
  | .value v => .value (f v)
  | .fault e => .fault e
  | .resourceLimit l => .resourceLimit l

/-- The outcome of `f` on the value of an outcome; a fault or a limit stops
the computation and is the result. -/
def Outcome.bind {α β : Type} : Outcome α → (α → Outcome β) → Outcome β
  | .value v, f => f v
  | .fault e, _ => .fault e
  | .resourceLimit l, _ => .resourceLimit l

instance : Monad Outcome where
  pure := .value
  map := Outcome.map
  bind := Outcome.bind

/-- The outcome of an operation that is given where it is defined: the value
`a` of `some a`, and the fault `e` for `none`, where it is undefined. -/
def FieldError.lift {α : Type} (e : FieldError) : Option α → Outcome α
  | some a => .value a
  | none => .fault e

/-! ## Checks of the limits

kalyx runs every operation in one order (numbers contract, "Checks and
charges"): first the domain tests of the operation, such as the test of a zero
divisor, then the check of a bound on the bits of its result, computed from
the operands alone, against `maxIntegerBits`, and only then the computation,
whose result is checked once more. A domain error is therefore never replaced
by `ResourceLimit`, under any limits. A check that compares an amount with a
limit and so decides the outcome, as an exponent is compared with
`maxExponent`, is `checkLimit`. The bit checks are stated in the form that
may report (`SizeCheck`): from a stated estimate of the bits of the result,
computed from the operands, and from the bits of the result itself. -/

/-- A check that decides: `ResourceLimit` naming `field` when `amount` is above
`limit`, and otherwise `next`, the outcome of the rest of the operation. -/
def checkLimit {α : Type} (field : LimitField) (limit amount : ℕ) (next : Outcome α) :
    Outcome α :=
  if limit < amount then .resourceLimit field else next

/-- The bit checks of an operation on given operands: `estimateAbove`, a stated
estimate of the bits of the result, computed from the operands, is above the
limit; `above`, a result is above the limit. -/
structure SizeCheck (α : Type) where
  /-- The estimate computed from the operands is above the limit. -/
  estimateAbove : Prop
  /-- A result is above the limit. -/
  above : α → Prop

/-- The checks of the estimate `bound` and of the bits `bits` of a result
against `limit`. -/
def SizeCheck.ofBound {α : Type} (limit bound : ℕ) (bits : α → ℕ) : SizeCheck α where
  estimateAbove := limit < bound
  above a := limit < bits a

/-- The outcomes that the checks `c`, which report `ResourceLimit` naming
`field`, admit for an operation whose outcome without these checks is
`domain`: the value of `domain` when it is not above the limit; the fault of
`domain`, which no check replaces; a `ResourceLimit` that `domain` already
reports; and `ResourceLimit` naming `field` in place of a value where the
estimate or the value is above the limit. Where the estimate bounds the bits
of every result, a limit at or above the estimate admits only the value of
`domain`, and a limit below it admits `ResourceLimit`: the operation may
report it. -/
def SizeCheck.Admits {α : Type} (c : SizeCheck α) (field : LimitField) (domain : Outcome α) :
    Outcome α → Prop
  | .value a => domain = .value a ∧ ¬c.above a
  | .fault e => domain = .fault e
  | .resourceLimit f =>
    domain = .resourceLimit f ∨ (f = field ∧ ∃ a, domain = .value a ∧ (c.estimateAbove ∨ c.above a))

end Kalyx.Spec.Fields

end
