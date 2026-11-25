module

public import Kalyx.Statements.Polynomials
import Kalyx.Proofs.Polynomials.Checks

/-!
# Proofs of the statements about the ring operations

One theorem for each registered statement of `Kalyx.Statements.Polynomials`
about the ring operations and the derivative, whose type is exactly that
statement. They state that the operations return canonical polynomials that
denote the operations of Mathlib's `Polynomial`, and that the derivative
follows the product rule.

The proofs rest on the helper modules of this directory. Canonical
polynomials are determined by their interpretation, since the coefficient of
the interpretation at a stored degree is the interpretation of the stored
coefficient and zero elsewhere (`Kalyx.Proofs.Polynomials.Canonical`). The
writer never reports `Internal` on canonical operands, and each loop over
terms (the merge of sums and differences, the rows of a product, the terms of
the derivative) keeps a canonical accumulated polynomial below the degrees
still to be written that denotes the partial result
(`Kalyx.Proofs.Polynomials.Operations`). A check passes its polynomial on or
reports `ResourceLimit`, so the operations of a ring are the operations
without the checks with their results and the partial sums of products
checked, and a power is an induction over the binary digits of its exponent
(`Kalyx.Proofs.Polynomials.Checks`). The rules for the sum and the product of
derivatives then follow from Mathlib's `derivative_add` and `derivative_mul`
and from uniqueness.
-/

namespace Kalyx.Proofs.Polynomials

open Kalyx.Spec.Fields Kalyx.Spec.Polynomials Kalyx.Statements.Polynomials Polynomial
open Kalyx.Proofs.Polynomials.Canonical Kalyx.Proofs.Polynomials.Operations
open Kalyx.Proofs.Polynomials.Checks

/-- Proves `RingOperationsAreExact`. -/
public theorem ringOperationsAreExact : RingOperationsAreExact := by
  intro P E K _ R M hR
  refine ⟨fun r a b ha hb h => eq_of_interpret_eq M r.coefficients (hR.1.unique _) ha hb h,
    fun p a ha => negate_spec hR ha,
    fun p a b ha hb => ⟨sum_spec hR ha hb, difference_spec hR ha hb, product_spec hR ha hb⟩,
    fun p d c hc => monomial_spec hR.2 d hc, fun L r => ?_⟩
  exact ⟨zero_ywl L r, one_ywl hR L r, generator_ywl hR L r, fun c hc => constant_ywl hR L r hc,
    fun a ha => ⟨negate_ywl hR L r ha, power_ywl hR L r ha, power_zero_exponent L r a⟩,
    fun a b ha hb => ⟨add_ywl hR L r ha hb, subtract_ywl hR L r ha hb, multiply_ywl hR L r ha hb⟩,
    fun k hk1 hk2 => power_zero_base L r hk1 hk2⟩

/-- Proves `DerivativeFollowsTheProductRule`. -/
public theorem derivativeFollowsTheProductRule : DerivativeFollowsTheProductRule := by
  intro P E K _ R M hR
  refine ⟨fun p a ha => derivative_spec hR ha, fun L r a ha => derivative_ywl hR L r ha,
    fun p a b ha hb => ⟨?_, ?_⟩⟩
  · obtain ⟨s, hs, hsc, hsi⟩ := sum_spec hR ha hb
    obtain ⟨s', hs', hs'c, hs'i⟩ := derivative_spec hR hsc
    obtain ⟨a', ha', ha'c, ha'i⟩ := derivative_spec hR ha
    obtain ⟨b', hb', hb'c, hb'i⟩ := derivative_spec hR hb
    obtain ⟨t, ht, htc, hti⟩ := sum_spec hR ha'c hb'c
    simp only [hs, bind_eq_bind, bind_value, hs', ha', hb', ht]
    congr 1
    refine eq_of_interpret_eq M p (hR.1.unique p) hs'c htc ?_
    rw [hs'i, hti, ha'i, hb'i, hsi, derivative_add]
  · obtain ⟨s, hs, hsc, hsi⟩ := product_spec hR ha hb
    obtain ⟨s', hs', hs'c, hs'i⟩ := derivative_spec hR hsc
    obtain ⟨a', ha', ha'c, ha'i⟩ := derivative_spec hR ha
    obtain ⟨b', hb', hb'c, hb'i⟩ := derivative_spec hR hb
    obtain ⟨u, hu, huc, hui⟩ := product_spec hR ha'c hb
    obtain ⟨v, hv, hvc, hvi⟩ := product_spec hR ha hb'c
    obtain ⟨t, ht, htc, hti⟩ := sum_spec hR huc hvc
    simp only [hs, bind_eq_bind, bind_value, hs', ha', hb', hu, hv, ht]
    congr 1
    refine eq_of_interpret_eq M p (hR.1.unique p) hs'c htc ?_
    rw [hs'i, hti, hui, hvi, ha'i, hb'i, hsi, derivative_mul]

end Kalyx.Proofs.Polynomials
