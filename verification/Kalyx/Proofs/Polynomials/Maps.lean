module

public import Kalyx.Statements.Polynomials
import Kalyx.Proofs.Polynomials.Evaluation
import Kalyx.Proofs.Polynomials.Mapping

/-!
# Proofs of the statements about evaluation and maps

One theorem for each registered statement of `Kalyx.Statements.Polynomials`
about evaluation and the maps of polynomials, whose type is exactly that
statement. They state that evaluation is a homomorphism and that a map acts on
each coefficient.

Evaluation adds the products of the coefficients and the powers of the
element in the stored order of the terms, and each power is formed by
repeated squaring, so by induction over the terms and over the binary digits
of each degree its value is a canonical element that denotes Mathlib's
`eval` (`Kalyx.Proofs.Polynomials.Evaluation`); the sum, the product and the
polynomial one then follow from Mathlib's `eval_add`, `eval_mul` and
`eval_one` and from the uniqueness of canonical elements. The meaning of a
map on the polynomials of Mathlib is the image of the polynomial over the
domain that a polynomial comes from, read coefficient by coefficient; the map
of a canonical polynomial writes the image of each coefficient after its zero
test, so it denotes that image, or reaches `notInDomain` at the first
coefficient outside the domain (`Kalyx.Proofs.Polynomials.Mapping`).
-/

namespace Kalyx.Proofs.Polynomials

open Kalyx.Spec.Fields Kalyx.Spec.Polynomials Kalyx.Statements.Polynomials Polynomial
open Kalyx.Proofs.Polynomials.Canonical Kalyx.Proofs.Polynomials.Operations
open Kalyx.Proofs.Polynomials.Evaluation Kalyx.Proofs.Polynomials.Mapping

/-- Proves `EvaluationIsAHomomorphism`. -/
public theorem evaluationIsAHomomorphism : EvaluationIsAHomomorphism := by
  refine ⟨fun P E U K _ R M hR p a c ha hc => eval_spec hR ha hc,
    fun P E K _ R M hR p a b c ha hb hc => ⟨?_, ?_, ?_⟩⟩
  · obtain ⟨s, hs, hsc, hsi⟩ := sum_spec hR ha hb
    obtain ⟨es, hes, hesc, hesi⟩ := eval_spec hR.1 hsc hc
    obtain ⟨ea, hea, heac, heai⟩ := eval_spec hR.1 ha hc
    obtain ⟨eb, heb, hebc, hebi⟩ := eval_spec hR.1 hb hc
    obtain ⟨e, he, hec, hei⟩ := hR.1.add p ea eb heac hebc
    simp only [hs, bind_eq_bind, bind_value, hes, hea, heb, he, ofOutcome_value]
    congr 1
    exact hR.1.unique p _ _ hesc hec (by rw [hesi, hei, hsi, eval_add, heai, hebi])
  · obtain ⟨s, hs, hsc, hsi⟩ := product_spec hR ha hb
    obtain ⟨es, hes, hesc, hesi⟩ := eval_spec hR.1 hsc hc
    obtain ⟨ea, hea, heac, heai⟩ := eval_spec hR.1 ha hc
    obtain ⟨eb, heb, hebc, hebi⟩ := eval_spec hR.1 hb hc
    obtain ⟨e, he, hec, hei⟩ := hR.1.multiply p ea eb heac hebc
    simp only [hs, bind_eq_bind, bind_value, hes, hea, heb, he, ofOutcome_value]
    congr 1
    exact hR.1.unique p _ _ hesc hec (by rw [hesi, hei, hsi, eval_mul, heai, hebi])
  · obtain ⟨s, hs, hsc, hsi⟩ := monomial_spec hR.2 0 (hR.1.one p).1
    obtain ⟨es, hes, hesc, hesi⟩ := eval_spec hR.1 hsc hc
    simp only [hs, bind_value, hes]
    congr 1
    refine hR.1.unique p _ _ hesc (hR.1.one p).1 ?_
    rw [hesi, hsi, (hR.1.one p).2, monomial_zero_left, map_one, eval_one]

/-- Proves `MapsActOnEachCoefficient`. -/
public theorem mapsActOnEachCoefficient : MapsActOnEachCoefficient :=
  ⟨fun _ _ _ _ φ A => ⟨mapPoly_none_iff φ A, mapPoly_eq_some_iff φ A⟩,
    fun _ _ _ _ φ _ _ _ _ hA hB => ⟨mapPoly_add φ hA hB, mapPoly_mul φ hA hB⟩,
    fun _ _ _ _ g A => mapPoly_ofRingHom g A,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hR hf _ ha => map_spec hR hf ha⟩

end Kalyx.Proofs.Polynomials
