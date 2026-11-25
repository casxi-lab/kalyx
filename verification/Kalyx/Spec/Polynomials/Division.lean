module

public import Kalyx.Spec.Polynomials.Arithmetic

/-!
# Polynomials: division, GCDs and modular powers

The shared algorithms of the univariate polynomials over a coefficient field
(architecture, "Coefficient-field trait"): division with remainder and the
remainder alone (FLD-R08), the monic form and the monic GCD by the Euclidean
algorithm (FLD-R09), the extended GCD with the cofactors of lowest degree
(POL-R12), and modular powers (POL-R13). Each is written once, for every
coefficient field whose zero test always decides (POL-R10): it reaches the
coefficients only through the methods of the trait (`CoefficientField`), and
builds every polynomial with the operations without the checks of
`Kalyx.Spec.Polynomials.Arithmetic`, whose merges and rows test each
computed coefficient for zero, so that every result is written by the one
writer of the terms. The only division of coefficients is the inverse of a
leading coefficient, which the coefficient field computes; no coefficient is
divided by an integer.

The algorithms read no limits: the checks and the charges of a request
context are not part of this specification, and a fault or a limit of a
coefficient operation ends an algorithm and is its result, passed on
unchanged. A division by the zero polynomial fails with `DivisionByZero`, a
fault of the coefficient fields, before anything else.

The loops are bounded by a number of steps, the fuel, that their results
never reach on canonical operands over a field that satisfies the laws of the
coefficient fields: each step of a long division lowers the degree of the
working remainder, and each step of the Euclidean algorithms lowers the degree
of the next remainder. Running out of steps is `Internal`, as a broken
invariant is.
-/

@[expose] public section

namespace Kalyx.Spec.Polynomials

open Kalyx.Spec.Fields (CoefficientField CoefficientRing)

variable {P E : Type}

/-! ## Scaling and the monic form -/

/-- The product of the polynomial `a` with the element `u`: the row
`u x^0 · a`, each coefficient tested for zero. -/
def Poly.scale (R : CoefficientRing P E Empty) (p : P) (u : E) (a : Poly E) :
    PolyResult (Poly E) :=
  Poly.zero.row R p 0 u a.terms

/-- The monic form of `a` (FLD-R09): `a` multiplied by the inverse of its
leading coefficient, so that its leading coefficient is one; the zero
polynomial for the zero polynomial. -/
def Poly.monicForm (F : CoefficientField P E Empty) (p : P) (a : Poly E) :
    PolyResult (Poly E) :=
  match a.leadingCoefficient with
  | none => .value Poly.zero
  | some c => do Poly.scale F.toCoefficientRing p (← PolyResult.ofOutcome (F.inverse p c)) a

/-! ## Division with remainder

Long division by a nonzero `b`, whose leading term is `l x^m`: while the
working remainder `w`, which starts as the dividend, is not zero and its
degree `d` is at least `m`, its leading term `c x^d` is cancelled by the
quotient term `t = (c l⁻¹) x^(d - m)`, which is added to the quotient, and
`w` becomes `w - t b`. The quotient and the remainder are the quotient and the
last working remainder, so `a = q b + r` with `deg r < deg b`; these two
conditions determine them (FLD-R08). The inverse `l⁻¹` is computed once. -/

/-- One step of long division by `b`, of degree `m` and with the inverse `u`
of its leading coefficient, on the working remainder `w`, whose leading term
is `c x^d`: the quotient term `t = (c u) x^(d - m)`, and `w - t b`. -/
def Poly.divisionStep (R : CoefficientRing P E Empty) (p : P) (b : Poly E) (m : ℕ) (u : E)
    (w : Poly E) (d : ℕ) (c : E) : PolyResult (Poly E × Poly E) := do
  let t ← Poly.monomial R p (d - m) (← PolyResult.ofOutcome (R.multiply p c u))
  pure (t, ← Poly.difference R p w (← Poly.product R p .value t b))

/-- At most `fuel` steps of long division by `b`, of degree `m` and with the
inverse `u` of its leading coefficient, from the quotient `q` and the working
remainder `w`: while the degree of `w` is at least `m`, a step
(`Poly.divisionStep`) adds its quotient term to `q` and replaces `w`; then the
quotient and the remainder `(q, w)`. Running out of steps is `Internal`. -/
def Poly.longDivision (R : CoefficientRing P E Empty) (p : P) (b : Poly E) (m : ℕ) (u : E) :
    ℕ → Poly E → Poly E → PolyResult (Poly E × Poly E)
  | fuel, q, w =>
    match w.terms.getLast? with
    | some (d, c) =>
      if m ≤ d then
        match fuel with
        | 0 => .fault (.term .internal)
        | fuel + 1 => do
          let (t, w) ← Poly.divisionStep R p b m u w d c
          Poly.longDivision R p b m u fuel (← Poly.sum R p q t) w
      else .value (q, w)
    | none => .value (q, w)
termination_by structural fuel => fuel

/-- At most `fuel` steps of long division by `b` that keep only the working
remainder `w`: the same steps as `Poly.longDivision`, without the quotient;
then the remainder. -/
def Poly.remainderSteps (R : CoefficientRing P E Empty) (p : P) (b : Poly E) (m : ℕ) (u : E) :
    ℕ → Poly E → PolyResult (Poly E)
  | fuel, w =>
    match w.terms.getLast? with
    | some (d, c) =>
      if m ≤ d then
        match fuel with
        | 0 => .fault (.term .internal)
        | fuel + 1 => do
          let (_, w) ← Poly.divisionStep R p b m u w d c
          Poly.remainderSteps R p b m u fuel w
      else .value w
    | none => .value w
termination_by structural fuel => fuel

/-- Division with remainder of `a` by `b` over a coefficient field (FLD-R08):
`DivisionByZero` for the zero polynomial `b`; otherwise the quotient and the
remainder `(q, r)` of long division, from the quotient zero and the working
remainder `a`, in at most `deg a + 1` steps. -/
def Poly.divRem (F : CoefficientField P E Empty) (p : P) (a b : Poly E) :
    PolyResult (Poly E × Poly E) :=
  match b.terms.getLast? with
  | none => .fault (.field .divisionByZero)
  | some (m, l) => do
    let u ← PolyResult.ofOutcome (F.inverse p l)
    Poly.longDivision F.toCoefficientRing p b m u (a.degree.getD 0 + 1) Poly.zero a

/-- The remainder of `a` by `b` alone: `DivisionByZero` for the zero
polynomial `b`; otherwise the remainder of long division, without the
quotient, which is the remainder of `Poly.divRem`. -/
def Poly.rem (F : CoefficientField P E Empty) (p : P) (a b : Poly E) : PolyResult (Poly E) :=
  match b.terms.getLast? with
  | none => .fault (.field .divisionByZero)
  | some (m, l) => do
    let u ← PolyResult.ofOutcome (F.inverse p l)
    Poly.remainderSteps F.toCoefficientRing p b m u (a.degree.getD 0 + 1) a

/-! ## The monic GCD -/

/-- At most `fuel` steps of the Euclidean algorithm on the remainders `r₀` and
`r₁`: while `r₁` is not zero, a step goes on with `r₁` and the remainder of
`r₀` by `r₁`; then `r₀`, the last remainder that is not zero, or zero when
both inputs are zero. Running out of steps is `Internal`. -/
def Poly.euclid (F : CoefficientField P E Empty) (p : P) :
    ℕ → Poly E → Poly E → PolyResult (Poly E)
  | fuel, r₀, r₁ =>
    if r₁.isZero then .value r₀
    else
      match fuel with
      | 0 => .fault (.term .internal)
      | fuel + 1 => do Poly.euclid F p fuel r₁ (← Poly.rem F p r₀ r₁)
termination_by structural fuel => fuel

/-- The monic GCD of `a` and `b` over a coefficient field (FLD-R09): the monic
form of the last nonzero remainder of the Euclidean algorithm on `a` and `b`,
in at most `deg b + 1` steps. So `gcd(0, 0) = 0`, `gcd(a, 0)` is the monic
form of `a`, and the GCD of two polynomials that are not both zero is the
monic polynomial that divides both and that every common divisor divides,
which these conditions determine; it is `1` exactly when they are coprime. -/
def Poly.monicGcd (F : CoefficientField P E Empty) (p : P) (a b : Poly E) :
    PolyResult (Poly E) := do
  Poly.monicForm F p (← Poly.euclid F p (b.degree.getD 0 + 1) a b)

/-! ## The extended GCD -/

/-- The result of the extended GCD of `a` and `b`: the left and the right
cofactors `s` and `t` and the monic GCD `g`, with `s a + t b = g`. The states
of the extended Euclidean algorithm have the same form: a remainder in the
field `gcd`, with its cofactors. -/
structure Bezout (E : Type) where
  /-- The left cofactor `s`, of `a`. -/
  left : Poly E
  /-- The right cofactor `t`, of `b`. -/
  right : Poly E
  /-- The monic GCD `g`, or the remainder of a state. -/
  gcd : Poly E
  deriving DecidableEq, Repr

/-- At most `fuel` steps of the extended Euclidean algorithm from the states
`x` and `y`, each a remainder with its cofactors: while the remainder of `y`
is not zero, a step divides the remainder of `x` by that of `y`, with the
quotient `q` and the remainder `r`, and goes on with `y` and the state of `r`,
whose cofactors are those of `x` less `q` times those of `y`; then `x`.
Running out of steps is `Internal`. -/
def Poly.extendedEuclid (F : CoefficientField P E Empty) (p : P) :
    ℕ → Bezout E → Bezout E → PolyResult (Bezout E)
  | fuel, x, y =>
    if y.gcd.isZero then .value x
    else
      match fuel with
      | 0 => .fault (.term .internal)
      | fuel + 1 => do
        let R := F.toCoefficientRing
        let (q, r) ← Poly.divRem F p x.gcd y.gcd
        let s ← Poly.difference R p x.left (← Poly.product R p .value q y.left)
        let t ← Poly.difference R p x.right (← Poly.product R p .value q y.right)
        Poly.extendedEuclid F p fuel y ⟨s, t, r⟩
termination_by structural fuel => fuel

/-- The extended GCD of `a` and `b` over a coefficient field (POL-R12): the
extended Euclidean algorithm from the states `(1, 0, a)` and `(0, 1, b)`, in
at most `deg b + 1` steps, whose last state, the last nonzero remainder with
its cofactors, is multiplied by the inverse of the leading coefficient of the
remainder; `(0, 0, 0)` when `a` and `b` are both zero. The GCD is that of
`Poly.monicGcd`, and the cofactors are those of lowest degree
(`Poly.lowestCofactors`). -/
def Poly.extendedGcd (F : CoefficientField P E Empty) (p : P) (a b : Poly E) :
    PolyResult (Bezout E) := do
  let R := F.toCoefficientRing
  let one ← Poly.monomial R p 0 (R.one p)
  let e ← Poly.extendedEuclid F p (b.degree.getD 0 + 1) ⟨one, Poly.zero, a⟩ ⟨Poly.zero, one, b⟩
  match e.gcd.leadingCoefficient with
  | none => pure ⟨Poly.zero, Poly.zero, Poly.zero⟩
  | some c => do
    let u ← PolyResult.ofOutcome (F.inverse p c)
    pure ⟨← Poly.scale R p u e.left, ← Poly.scale R p u e.right, ← Poly.scale R p u e.gcd⟩

/-- Whether `s` and `t` are the cofactors of lowest degree of `a` and `b` with
the monic GCD `g` (POL-R12), read from the degrees of canonical polynomials.
The cofactors with `s a + t b = g` are unique up to adding `k b/g` to `s` and
subtracting `k a/g` from `t`; the conditions pick one pair:

* `b` zero: `t` is zero, and `s` is zero when `a` is zero too, so
  `(0, 0, 0)` for `a = b = 0`;
* `b` a nonzero constant multiple of `g`, `deg b = deg g`: `s` is zero, also
  when `a` is a constant multiple of `g`, or zero;
* `a` a nonzero constant multiple of `g` and `b` not: `t` is zero;
* otherwise, when neither is a constant multiple of `g`:
  `deg s + deg g < deg b` and `deg t + deg g < deg a`.

The first two cases leave `t` and the third `s` determined by `s a + t b = g`,
and in the last the bound on `s` determines it. A `g` of no degree with a
nonzero `b` is not a GCD of `b`, and no cofactors fit it. -/
def Poly.lowestCofactors (a b s t g : Poly E) : Bool :=
  match b.degree, g.degree with
  | none, _ => t.isZero && (!a.isZero || s.isZero)
  | some db, some dg =>
    if db = dg then s.isZero
    else if a.degree = some dg then t.isZero
    else s.degree.all (· + dg < db) && t.degree.all (· + dg < a.degree.getD 0)
  | some _, none => false

/-! ## Modular powers -/

/-- The power `a^k` modulo `m` over a coefficient field (POL-R13):
`DivisionByZero` for the zero polynomial `m`; otherwise, with `a` and the
polynomial one each first reduced modulo `m`, the power starts from the
reduced one, and each binary digit of `k`, from the highest, squares it and,
for a digit 1, multiplies it by the reduced `a`, each product reduced modulo
`m`. So the result is the remainder of `a^k` by `m`, of degree below that of
`m`; for `k = 0` it is the remainder of one, which is zero for a constant
`m`. -/
def Poly.powerMod (F : CoefficientField P E Empty) (p : P) (a : Poly E) (k : ℕ) (m : Poly E) :
    PolyResult (Poly E) :=
  let R := F.toCoefficientRing
  if m.isZero then .fault (.field .divisionByZero)
  else do
    let a ← Poly.rem F p a m
    let one ← Poly.rem F p (← Poly.monomial R p 0 (R.one p)) m
    (binaryDigits k).foldlM (init := one) fun s digit => do
      let s ← Poly.rem F p (← Poly.product R p .value s s) m
      if digit then Poly.rem F p (← Poly.product R p .value s a) m else pure s

end Kalyx.Spec.Polynomials

end
