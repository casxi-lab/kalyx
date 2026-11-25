module

public import Kalyx.Statements.Polynomials
import Kalyx.Proofs.Polynomials.Checks
import Kalyx.Proofs.Polynomials.Euclid

/-!
# Proofs of the statements about division and the GCDs

One theorem for each registered statement of `Kalyx.Statements.Polynomials`
about the shared algorithms over a coefficient field, whose type is exactly
that statement. They state that division with remainder, the monic GCD and the
extended GCD with the cofactors of lowest degree are determined by their
defining conditions, and that modular powers are remainders.

The proofs rest on the helper modules of this directory. Each step of long
division cancels the leading term of the working remainder with a quotient
term whose product with the divisor has the same leading term, so the degree
drops and the fuel suffices; long division keeps `A = q B + w`, and the loop
of the remainder alone takes the same steps
(`Kalyx.Proofs.Polynomials.Remainders`). The quotient and the remainder are
then determined by Mathlib's degree argument: the difference of two
remainders is a multiple of the divisor of lower degree. The Euclidean
algorithm keeps the common divisors of its two remainders, so the monic form
of its last nonzero remainder is a monic GCD, unique since two monic
associated polynomials are equal; the extended algorithm also keeps
`s A + t B = r` and bounds on the degrees of the cofactors of consecutive
states, which give the conditions of the cofactors of lowest degree, and the
cofactors with these conditions are unique since `B / g` divides the
difference of two left cofactors (`Kalyx.Proofs.Polynomials.Euclid`). A
modular power is an induction over the binary digits of its exponent, each
square and product reduced to a remainder congruent to the power read so far.
-/

namespace Kalyx.Proofs.Polynomials

open Kalyx.Spec.Fields Kalyx.Spec.Polynomials Kalyx.Statements.Polynomials Polynomial
open Kalyx.Proofs.Polynomials.Canonical Kalyx.Proofs.Polynomials.Operations
open Kalyx.Proofs.Polynomials.Checks Kalyx.Proofs.Polynomials.Remainders
open Kalyx.Proofs.Polynomials.Euclid

/-- Proves `DivisionWithRemainderIsUnique`. -/
public theorem divisionWithRemainderIsUnique : DivisionWithRemainderIsUnique := by
  intro P E K _ F M hF
  refine ⟨fun p a => ⟨divRem_zero a, rem_zero a⟩, fun p a b ha hb hb0 => ?_⟩
  obtain ⟨q, r, h1, h2, hqc, hrc, hi, hrd⟩ := divRem_spec hF ha hb hb0
  have hB : b.interpret M p ≠ 0 := fun h => hb0 ((interpret_eq_zero_iff M p hb).1 h)
  exact ⟨q, r, h1, hqc, hrc, hi, hrd, fun Q₁ R₁ h h' => divRem_unique hB hi hrd h h', h2⟩

/-- Proves `MonicGcdIsUnique`. -/
public theorem monicGcdIsUnique : MonicGcdIsUnique := by
  intro P E K _ F M hF
  refine ⟨fun p a ha => ⟨monicForm_spec hF ha, rfl⟩, fun p a b ha hb => ?_⟩
  obtain ⟨g, hg, hgc, hgG⟩ := monicGcd_spec hF ha hb
  exact ⟨g, hg, hgc, hgG, fun G hG => monicGcdOf_unique hG hgG, isRelPrime_iff hgG⟩

/-- Proves `ExtendedGcdHasLowestCofactors`. -/
public theorem extendedGcdHasLowestCofactors : ExtendedGcdHasLowestCofactors := by
  intro P E K _ F M hF p a b ha hb
  exact extendedGcd_spec hF ha hb

/-- Proves `ModularPowersAreRemainders`. -/
public theorem modularPowersAreRemainders : ModularPowersAreRemainders := by
  intro P E K _ F M hF
  refine ⟨fun p a k => rfl, fun p a k m ha hm hm0 => ?_⟩
  have hmz : m.isZero = false := by
    cases h : m.isZero
    · rfl
    · exact absurd ((isZero_iff m).1 h) hm0
  obtain ⟨a', ha', ha'c, ha'd, Qa, hQa⟩ := rem_spec hF ha hm hm0
  obtain ⟨o, ho, hoc, hoi⟩ := monomial_spec hF.1.2 0 (hF.1.1.one p).1
  obtain ⟨one, hone, honec, honed, Q1, hQ1⟩ := rem_spec hF hoc hm hm0
  have key := foldlM_binaryDigits
    (fun s j => s.Canonical M p ∧ (s.interpret M p).degree < (m.interpret M p).degree ∧
      ∃ Q, a.interpret M p ^ j = Q * m.interpret M p + s.interpret M p)
    (fun (s : Poly E) (digit : Bool) => do
      let s ← Poly.rem F p (← Poly.product F.toCoefficientRing p .value s s) m
      if digit then Poly.rem F p (← Poly.product F.toCoefficientRing p .value s a') m
      else pure s)
    ?_ k (s := one) ⟨honec, honed, Q1, by
      rw [pow_zero, ← hQ1, hoi, (hF.1.1.one p).2, monomial_zero_left, map_one]⟩
  · obtain ⟨s, hs, hsc, hsd, Q, hQ⟩ := key
    refine ⟨s, ?_, hsc, hsd, Q, hQ⟩
    simp only [Poly.powerMod, hmz, Bool.false_eq_true, ↓reduceIte, bind_eq_bind, ha',
      bind_value, ho, hone]
    exact hs
  · rintro s j digit ⟨hsc, -, Q, hQ⟩
    obtain ⟨s2, hs2, hs2c, hs2i⟩ := product_spec hF.1 hsc hsc
    obtain ⟨s3, hs3, hs3c, hs3d, Q3, hQ3⟩ := rem_spec hF hs2c hm hm0
    have h2 : a.interpret M p ^ (2 * j) =
        (Q * Q * m.interpret M p + 2 * Q * s.interpret M p + Q3) * m.interpret M p +
          s3.interpret M p := by
      linear_combination (a.interpret M p ^ j + Q * m.interpret M p + s.interpret M p) * hQ -
        hs2i + hQ3
    cases digit with
    | false =>
      refine ⟨s3, ?_, hs3c, hs3d, _, by simpa using h2⟩
      simp only [hs2, bind_eq_bind, bind_value, hs3, Bool.false_eq_true, ↓reduceIte, pure_eq_value]
    | true =>
      obtain ⟨s4, hs4, hs4c, hs4i⟩ := product_spec hF.1 hs3c ha'c
      obtain ⟨s5, hs5, hs5c, hs5d, Q5, hQ5⟩ := rem_spec hF hs4c hm hm0
      refine ⟨s5, ?_, hs5c, hs5d, ?_⟩
      · simp only [hs2, bind_eq_bind, bind_value, hs3, ↓reduceIte, hs4, hs5]
      · refine ⟨(Q * Q * m.interpret M p + 2 * Q * s.interpret M p + Q3) * Qa *
          m.interpret M p + (Q * Q * m.interpret M p + 2 * Q * s.interpret M p + Q3) *
          a'.interpret M p + s3.interpret M p * Qa + Q5, ?_⟩
        rw [Bool.toNat_true, pow_succ]
        linear_combination a.interpret M p * h2 +
          ((Q * Q * m.interpret M p + 2 * Q * s.interpret M p + Q3) * m.interpret M p +
            s3.interpret M p) * hQa - hs4i + hQ5

end Kalyx.Proofs.Polynomials
