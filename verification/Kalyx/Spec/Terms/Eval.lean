module

public import Kalyx.Spec.Terms.Order

/-!
# Terms: what `eval` reads

The operation `eval` reads the canonical term of its input (terms contract,
"Evaluation of a request", TRM-R12): an input whose canonical term cannot be
built fails with the error of building it, a canonical term that holds a free
symbol fails with `UnknownSymbol`, and any other canonical term is the
answer, which need not be a number. On the terms of release 0.1, without
constants, calls and conditions, this is the rule of that release as the
terms contract states it: a canonical number gives itself, and a canonical
term that is not a number holds a symbol and fails.

The free symbols of a term skip the variable and binding positions of the
special forms (architecture, "Call nodes"). The table of the special forms,
which names those positions, is a parameter here (`EvalParams.skips`), and so
is the answer for a term without free symbols that holds a formal call: the
term as it is, or the state `Unevaluated` (`ClosedFormal`), which the design
leaves open. Reading the input, the roles of a request and the answer lines
are not part of the term core and not of this specification.
-/

@[expose] public section

namespace Kalyx.Spec.Terms

/-! ## Free symbols and formal calls -/

/-- The elements of a list whose positions, counted from `i`, `skip` does not
name. -/
def keepPositions {α : Type} (skip : ℕ → Bool) (i : ℕ) : List α → List α
  | [] => []
  | a :: as => (if skip i then [] else [a]) ++ keepPositions skip (i + 1) as
  termination_by structural as => as

mutual

/-- The free symbols of a term, in the order of their occurrences and with
repeats: the names of its symbols, except in the arguments of a call that
`skips` names for its head, the variable and binding positions of the special
forms. Numbers and constants hold none. -/
def Term.freeSymbols (skips : Head → ℕ → Bool) : Term → List String
  | .number _ | .constant _ => []
  | .symbol s => [s]
  | .call h args => (keepPositions (skips h) 0 (Term.freeSymbolsList skips args)).flatten
  | .power b _ => Term.freeSymbols skips b
  | .product _ fs => (Term.freeSymbolsList skips fs).flatten
  | .sum _ ms => Term.freeSymbolsPairs skips ms
  | .condition _ ops => (Term.freeSymbolsList skips ops).flatten
  termination_by structural t => t

/-- The free symbols of each term of a list, in order. -/
def Term.freeSymbolsList (skips : Head → ℕ → Bool) : List Term → List (List String)
  | [] => []
  | t :: ts => Term.freeSymbols skips t :: Term.freeSymbolsList skips ts
  termination_by structural ts => ts

/-- The free symbols of the cores of a list of monomials. -/
def Term.freeSymbolsPairs (skips : Head → ℕ → Bool) : List (ℚ × Term) → List String
  | [] => []
  | (_, t) :: ms => Term.freeSymbols skips t ++ Term.freeSymbolsPairs skips ms
  termination_by structural ms => ms

end

mutual

/-- Whether a term holds a call of the class `Formal`, a special form, at any
depth. -/
def Term.holdsFormal : Term → Bool
  | .number _ | .constant _ | .symbol _ => false
  | .call h args => h.callClass == .formal || Term.holdsFormalList args
  | .power b _ => Term.holdsFormal b
  | .product _ fs => Term.holdsFormalList fs
  | .sum _ ms => Term.holdsFormalPairs ms
  | .condition _ ops => Term.holdsFormalList ops
  termination_by structural t => t

/-- Whether a term of a list holds a formal call. -/
def Term.holdsFormalList : List Term → Bool
  | [] => false
  | t :: ts => Term.holdsFormal t || Term.holdsFormalList ts
  termination_by structural ts => ts

/-- Whether the core of a monomial of a list holds a formal call. -/
def Term.holdsFormalPairs : List (ℚ × Term) → Bool
  | [] => false
  | (_, t) :: ms => Term.holdsFormal t || Term.holdsFormalPairs ms
  termination_by structural ms => ms

end

/-! ## `eval` -/

/-- The answer of `eval` for a term without free symbols that holds a formal
call, such as a `substitute` or a `piecewise` whose condition is not a truth
value: the two answers that the design leaves open. -/
inductive ClosedFormal where
  /-- The canonical term, as for any other term. -/
  | asIs
  /-- The state `Unevaluated`. -/
  | unevaluated
  deriving DecidableEq, Repr

/-- What `eval` reads besides the term: the variable and binding positions of
the special forms, `skips h i` for the argument at the index `i`, counted from
0, of a call with the head `h`; and the answer for a term without free symbols
that holds a formal call. -/
structure EvalParams where
  /-- The positions that free symbols skip. -/
  skips : Head → ℕ → Bool
  /-- The answer for a term without free symbols that holds a formal call. -/
  closedFormal : ClosedFormal

/-- An answer of `eval`: a canonical term as the value, or the state
`Unevaluated` with the term that was not evaluated. -/
inductive EvalAnswer where
  /-- The canonical term as the value of the answer. -/
  | value (t : Term)
  /-- The state `Unevaluated`. -/
  | unevaluated (t : Term)
  deriving DecidableEq

/-- `eval` of a canonical term (TRM-R12): `UnknownSymbol` when it holds a free
symbol; otherwise the term itself, except that a term holding a formal call
gives what `closedFormal` names. For an input, `eval` is this function bound
to the result of building the canonical term, so an error of building is the
answer. -/
def Term.eval (p : EvalParams) (t : Term) : Result EvalAnswer :=
  if (t.freeSymbols p.skips).isEmpty then
    if t.holdsFormal && p.closedFormal == .unevaluated then .value (.unevaluated t)
    else .value (.value t)
  else .fault .unknownSymbol

end Kalyx.Spec.Terms

end
