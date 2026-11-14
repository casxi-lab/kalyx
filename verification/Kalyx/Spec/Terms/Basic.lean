module

public import Kalyx.Spec.Fields.Rationals
public import Kalyx.Spec.Fields.NumberField

/-!
# Terms: faults, results and exponents

The specification of the term core of kalyx (the terms and their kinds, the
total order, the canonical forms that the constructors keep, the display
text, the meaning of a term and what `eval` reads) is written from the
numbered requirements of the terms contract
(`docs/components/terms/contract.md`) and from the design rules of the
architecture (`docs/architecture.md`), not from the implementation. The
numbers in a term are the rationals of the specification of the coefficient
fields (`Kalyx.Spec.Fields`), which this specification imports and does not
restate: their canonical form, their operations and the bounds on their bits
are stated there. This module holds what all the parts share:

* `TermFault`, the faults that the term core reports, of which `Syntax` and
  `Unsupported` carry a span where the term core gives one;
* `Result`, the result of a construction: a value, a fault, or
  `ResourceLimit` naming a field of the limits (`LimitField` of the
  coefficient fields), with the lift of the outcomes of the coefficient
  fields;
* the check of an exponent against the explicit limit `maxExponent` and the
  width of `i64` (`exponentBound`, `checkExponent`).

The limits that a construction reads are explicit parameters, not a request
context. Work charges, the checks of nodes, storage bytes and depth before a
node is built, cancellation and deadlines are not part of this
specification.
-/

@[expose] public section

namespace Kalyx.Spec.Terms

open Kalyx.Spec.Fields (LimitField Outcome FieldError)

/-! ## Faults -/

/-- A half-open range of bytes, as kalyx's `Span`: its offsets count bytes
from 0, `start` is included and `stop` is excluded. -/
structure Span where
  /-- The first byte of the range. -/
  start : ℕ
  /-- The byte after the range. -/
  stop : ℕ
  deriving DecidableEq, Repr

/-- The faults that the term core reports, a part of the fault kinds of
kalyx. A fault of the term core carries no span, and the parser gives it the
span of the syntax node whose term failed; only the faults of a symbol name
(TRM-R11) carry a span of their own, into the name, so `Syntax` and
`Unsupported` take an optional span. -/
inductive TermFault where
  /-- `DivisionByZero`: a negative power of zero, or of a product with the
  coefficient 0. -/
  | divisionByZero
  /-- `OutsideDomain`. -/
  | outsideDomain
  /-- `Syntax`: a name that is not an identifier, with the span of its first
  character that the form does not allow, the empty span at 0 for the empty
  name; or an operand of the wrong class, a condition in a value position or
  a value in a condition position, without a span. -/
  | syntax (span : Option Span)
  /-- `Unsupported`: a reserved name, with the span of the whole name. -/
  | unsupported (span : Option Span)
  /-- `UnknownSymbol`: a term that `eval` reads holds a free symbol. -/
  | unknownSymbol
  /-- `InvalidBinding`. -/
  | invalidBinding
  /-- `Internal`: a defect of the library, never the result of a
  construction on canonical operands. -/
  | internal
  deriving DecidableEq, Repr

/-! ## Results -/

/-- The result of a construction: a value, a fault, or `ResourceLimit` naming
the field of the limits that a check found exceeded. -/
inductive Result (α : Type) where
  /-- The construction returns the value `v`. -/
  | value (v : α)
  /-- The construction fails with the fault `kind`. -/
  | fault (kind : TermFault)
  /-- The construction fails with `ResourceLimit` naming `field`. -/
  | resourceLimit (field : LimitField)
  deriving DecidableEq, Repr

/-- The result with `f` applied to its value; faults and limits are kept. -/
def Result.map {α β : Type} (f : α → β) : Result α → Result β
  | .value v => .value (f v)
  | .fault e => .fault e
  | .resourceLimit l => .resourceLimit l

/-- The result of `f` on the value of a result; a fault or a limit stops the
construction and is its result. -/
def Result.bind {α β : Type} : Result α → (α → Result β) → Result β
  | .value v, f => f v
  | .fault e, _ => .fault e
  | .resourceLimit l, _ => .resourceLimit l

instance : Monad Result where
  pure := .value
  map := Result.map
  bind := Result.bind

/-- The fault of the term core for a fault of the coefficient fields. The
rationals report only `DivisionByZero`; `VariableMismatch`, which values of
two different parents report, cannot arise from them and is `Internal`. -/
def TermFault.ofFieldError : FieldError → TermFault
  | .divisionByZero => .divisionByZero
  | .outsideDomain => .outsideDomain
  | .variableMismatch => .internal

/-- The outcome of an operation of the coefficient fields as a result: the
value, the fault by `TermFault.ofFieldError`, or the same limit. -/
def Result.ofOutcome {α : Type} : Outcome α → Result α
  | .value v => .value v
  | .fault e => .fault (TermFault.ofFieldError e)
  | .resourceLimit l => .resourceLimit l

/-! ## Exponents

An exponent of kalyx is an `i64`. Every exponent that the term core takes or
computes (the argument of a power, the sum of the exponents of one key in a
product, the product of two exponents in a power of a power) is checked
against `maxExponent` and the width of `i64` before it is used: the
effective bound is the smaller of `maxExponent` and `2⁶³ - 1`, and an
exponent of a larger magnitude fails with `ResourceLimit` naming
`max_exponent` (terms contract, "Exponents"). Exponents are integers here, so
sums and products of exponents are exact before the check, as in kalyx. The
check decides; it is the first step of a power, before its base is read. -/

/-- The default `max_exponent` of a request, 4096 (context contract). -/
def defaultMaxExponent : ℕ := 4096

/-- The default `max_integer_bits` of a request, 4096 (context contract). -/
def defaultMaxIntegerBits : ℕ := 4096

/-- The effective bound on the magnitude of an exponent under `maxExponent`:
the smaller of `maxExponent` and `2⁶³ - 1`, the largest `i64`. -/
def exponentBound (maxExponent : ℕ) : ℕ := min maxExponent (2 ^ 63 - 1)

/-- The check of the exponent `k` under `maxExponent`: `ResourceLimit` naming
`max_exponent` when the magnitude of `k` is above the effective bound, and
otherwise `next ()`, the rest of the construction, which is not computed when
the check fails. -/
def checkExponent {α : Type} (maxExponent : ℕ) (k : ℤ) (next : Unit → Result α) : Result α :=
  if exponentBound maxExponent < k.natAbs then .resourceLimit .exponent else next ()

end Kalyx.Spec.Terms

end
