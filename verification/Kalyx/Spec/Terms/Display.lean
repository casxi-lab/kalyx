module

public import Kalyx.Spec.Terms.Order

/-!
# Terms: the display text

`Term.display` writes the text of a term in the display grammar of the terms
contract ("Display", TRM-R10), with parentheses only where the grammar needs
them: numbers, symbols, integer powers, products and sums as the grammar
states them, the named constants by their names, and calls by their head
names and their arguments, so that `i π` and `2 i` are written `i*pi` and
`2*i` (architecture, "Reserved names"). The texts of algebraic constants and
of conditions are fixed with those kinds, not here, and are parameters
(`DisplayParams`). Factors and monomials are written in their stored order.

The text depends only on the term, so every way of building a term gives the
same text when the constructors give the same term. The check of each
written number against `max_integer_bits` and the charges for output are not
part of this specification.

Digits are written by structural recursion and texts are joined with `++`,
so the text of a given term reduces in the kernel.
-/

@[expose] public section

namespace Kalyx.Spec.Terms

/-! ## Numbers and joined texts -/

/-- The decimal digit of `d`, for `d < 10`. -/
def digitText : ℕ → String
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"

/-- The decimal digits of `n`, at most `fuel` of them. -/
def natTextAux : ℕ → ℕ → String
  | 0, _ => ""
  | fuel + 1, n => (if n < 10 then "" else natTextAux fuel (n / 10)) ++ digitText (n % 10)
  termination_by structural fuel _ => fuel

/-- The decimal digits of a natural number; `n` has at most `n + 1` digits. -/
def natText (n : ℕ) : String := natTextAux (n + 1) n

/-- The text of the magnitude of a rational: its numerator and, unless its
denominator is 1, `/` and its denominator. -/
def magnitudeText (q : ℚ) : String :=
  natText q.num.natAbs ++ if q.den = 1 then "" else "/" ++ natText q.den

/-- The text of a number: `-` when it is negative, then its magnitude, as
`-3/4`, `5` and `0`. -/
def ratText (q : ℚ) : String := (if q < 0 then "-" else "") ++ magnitudeText q

/-- The texts of a list joined by `sep`. -/
def joinText (sep : String) : List String → String
  | [] => ""
  | [s] => s
  | s :: t :: rest => s ++ sep ++ joinText sep (t :: rest)
  termination_by structural l => l

/-! ## Parts of the grammar -/

/-- The texts fixed with their kinds rather than here: of an algebraic
constant, by its identity and its type; and of a condition, from its shape
and the texts of its operands in order. -/
structure DisplayParams where
  /-- The text of an algebraic constant; not read for `π` and `i`. -/
  algebraic : Constant → String
  /-- The text of a condition from its shape and the texts of its operands. -/
  condition : CondShape → List String → String

/-- The text of a constant: the name of a named constant, `i` or `pi`, and
the text of the parameters for an algebraic constant. -/
def Constant.display (p : DisplayParams) : Constant → String
  | .named c => c.name
  | c => p.algebraic c

/-- Whether a base is written without parentheses in a power: a symbol, a
constant or a call, so `x^2`, `pi^(-1)` and `sin(x)^2`. -/
def Term.bareBase : Term → Bool
  | .symbol _ | .constant _ | .call .. => true
  | _ => false

/-- Whether a term is a sum. -/
def Term.isSum : Term → Bool
  | .sum .. => true
  | _ => false

/-- The text of an exponent: its digits when it is not negative, and `(-`,
the digits of its magnitude and `)` otherwise, as `2` and `(-1)`. -/
def exponentText (k : ℤ) : String :=
  if k < 0 then "(-" ++ natText k.natAbs ++ ")" else natText k.natAbs

/-- The prefix of the coefficient of a product: nothing for 1, `-` for `-1`,
and otherwise the number and `*`. -/
def coefficientPrefix (c : ℚ) : String :=
  if c = 1 then "" else if c = -1 then "-" else ratText c ++ "*"

/-- The texts of the factors `fs` of a product from their texts `ss`, each sum
among them in parentheses. -/
def factorTexts : List Term → List String → List String
  | f :: fs, s :: ss => (if f.isSum then "(" ++ s ++ ")" else s) :: factorTexts fs ss
  | _, _ => []
  termination_by structural fs _ => fs

/-- The text of a monomial after its separator, from its coefficient and the
text of its core: the magnitude of the coefficient and `*` unless that
magnitude is 1, then the core. -/
def monomialText (a : ℚ) (core : String) : String :=
  (if a = 1 ∨ a = -1 then "" else magnitudeText a ++ "*") ++ core

/-- The texts of monomials, each after its separator: ` - ` for a negative
coefficient and ` + ` otherwise, the coefficient 0 of a witness included. -/
def monomialsText : List (ℚ × String) → String
  | [] => ""
  | (a, s) :: ms => (if a < 0 then " - " else " + ") ++ monomialText a s ++ monomialsText ms
  termination_by structural ms => ms

/-- The text of a sum from its constant and its monomials with the texts of
their cores: the constant unless it is 0, then the monomials, each after its
separator; when the constant is 0, the first monomial has no separator and
only `-` for a negative coefficient. So `2 + x + y`, `1 - x`, `-x + y`,
`-2*x - y` and `5 + 0*x^(-1)`. -/
def sumText (c : ℚ) (ms : List (ℚ × String)) : String :=
  if c ≠ 0 then ratText c ++ monomialsText ms
  else match ms with
    | [] => ""
    | (a, s) :: rest => (if a < 0 then "-" else "") ++ monomialText a s ++ monomialsText rest

/-! ## The text of a term -/

mutual

/-- The display text of a term (TRM-R10): a number by `ratText`; a constant
by `Constant.display`; a symbol by its name; a call by its head name, `(`,
its arguments joined by `, `, and `)`; a power by its base, in parentheses
unless `Term.bareBase` holds, `^` and `exponentText` of its exponent; a
product by `coefficientPrefix` of its coefficient, then its factors joined by
`*`, each sum among them in parentheses; a sum by `sumText`; a condition by
the parameters. -/
def Term.display (p : DisplayParams) : Term → String
  | .number q => ratText q
  | .constant c => c.display p
  | .symbol s => s
  | .call h args => h.name ++ "(" ++ joinText ", " (Term.displayList p args) ++ ")"
  | .power b k =>
    let base := Term.display p b
    (if b.bareBase then base else "(" ++ base ++ ")") ++ "^" ++ exponentText k
  | .product c fs => coefficientPrefix c ++ joinText "*" (factorTexts fs (Term.displayList p fs))
  | .sum c ms => sumText c (Term.displayPairs p ms)
  | .condition s ops => p.condition s (Term.displayList p ops)
  termination_by structural t => t

/-- The display texts of a list of terms, in order. -/
def Term.displayList (p : DisplayParams) : List Term → List String
  | [] => []
  | t :: ts => Term.display p t :: Term.displayList p ts
  termination_by structural ts => ts

/-- The monomials of a sum, each with the display text of its core. -/
def Term.displayPairs (p : DisplayParams) : List (ℚ × Term) → List (ℚ × String)
  | [] => []
  | (a, t) :: ms => (a, Term.display p t) :: Term.displayPairs p ms
  termination_by structural ms => ms

end

end Kalyx.Spec.Terms

end
