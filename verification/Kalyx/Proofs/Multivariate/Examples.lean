module

public import Kalyx.Statements.Multivariate

/-!
# Proofs of the statements about the examples

One theorem for each registered statement of `Kalyx.Statements.Multivariate`
about the positive and the negative example of each requirement of the
multivariate contract, whose type is exactly that statement. The examples are
closed, so most are decided by evaluation in the kernel (`decide +kernel`),
which computes the comparisons, the operations, the expansion and the
conversion back to terms; the prime fields `𝔽_2` and `𝔽_5` are given as the
values that their constructor builds. Four examples need a proof beyond
evaluation: a canonical polynomial and the polynomial of Mathlib that it
denotes, and the lists that are not canonical, where canonicity is a
proposition and only its order and its coefficients are decided; that a ring
is determined by its data; and that every power `0ᵏ` with `k ≥ 1` is zero,
by induction over the binary digits below the highest, since the square of
zero and its product with zero are zero.
-/

namespace Kalyx.Proofs.Multivariate

open Kalyx.Spec.Fields Kalyx.Spec.Multivariate Kalyx.Statements.Multivariate

/-- The prime field `𝔽_2`. -/
private def two : PrimeField := ⟨2, by norm_num, by unfold WordModulus; norm_num⟩

/-- The constructor builds `𝔽_2` from `2`. -/
private theorem new_two : PrimeField.new 2 = .built two := by
  unfold PrimeField.new
  rw [dite_eq_left ⟨two.prime, two.word⟩]
  rfl

/-- The prime field `𝔽_5`. -/
private def five : PrimeField := ⟨5, by norm_num, by unfold WordModulus; norm_num⟩

/-- The constructor builds `𝔽_5` from `5`. -/
private theorem new_five : PrimeField.new 5 = .built five := by
  unfold PrimeField.new
  rw [dite_eq_left ⟨five.prime, five.word⟩]
  rfl

/-- Proves `ComparisonsUnderGrevlexAndABlockOrder`. -/
public theorem comparisonsUnderGrevlexAndABlockOrder : ComparisonsUnderGrevlexAndABlockOrder := by
  unfold ComparisonsUnderGrevlexAndABlockOrder
  decide +kernel

/-- Proves `ComparisonsOfOtherOrdersDoNotHold`. -/
public theorem comparisonsOfOtherOrdersDoNotHold : ComparisonsOfOtherOrdersDoNotHold := by
  unfold ComparisonsOfOtherOrdersDoNotHold
  decide +kernel

/-- Proves `CanonicalFormOfThreeTerms`. -/
public theorem canonicalFormOfThreeTerms : CanonicalFormOfThreeTerms := by
  unfold CanonicalFormOfThreeTerms
  dsimp only
  refine ⟨⟨_, rfl, ⟨?_, ?_⟩, ?_⟩, by decide +kernel,
    ⟨_, rfl, ⟨by simp [MvPoly.monomials, MvPoly.zero], by simp [MvPoly.coefficients, MvPoly.zero]⟩,
      by simp [MultivariateRing.model, MvPoly.interpret, MvPoly.zero]⟩, rfl⟩
  · simp only [ratRingXYZ, OrderKind.Lt]
    delta LexLT
    decide +kernel
  · simp [ratPoly, ratTerms, MvPoly.coefficients, Rationals.model, Fraction.Reduced, Fraction.ofRat,
      Fraction.interpret]
  · simp [MultivariateRing.model, MvPoly.interpret, ratPoly, ratTerms, Fraction.ofRat,
      Rationals.model, Fraction.interpret, Exponents.toFinsupp, MvPolynomial.monomial_eq,
      Finsupp.prod_fintype, Fin.prod_univ_three]
    ring

/-- Proves `NonCanonicalTermLists`. -/
public theorem nonCanonicalTermLists : NonCanonicalTermLists := by
  unfold NonCanonicalTermLists
  dsimp only
  refine ⟨fun h => (h.2 (Fraction.ofRat 0) ?_).2 (by decide +kernel), fun h => absurd h.1 ?_,
    fun h => absurd h.1 ?_⟩
  · simp [ratPoly, ratTerms, MvPoly.coefficients]
  all_goals
    simp only [OrderKind.Lt]
    delta LexLT
    decide +kernel

/-- Proves `RingsAreBuiltFromTheirData`. -/
public theorem ringsAreBuiltFromTheirData : RingsAreBuiltFromTheirData := by
  unfold RingsAreBuiltFromTheirData
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  rintro ⟨c, ns, h, o⟩ ⟨c', ns', h', o'⟩ hc hn ho
  simp_all

/-- Proves `RepeatedNamesAndDifferentRings`. -/
public theorem repeatedNamesAndDifferentRings : RepeatedNamesAndDifferentRings := by
  unfold RepeatedNamesAndDifferentRings
  decide +kernel

/-- Proves `LeadingMonomialsDependOnTheOrder`. -/
public theorem leadingMonomialsDependOnTheOrder : LeadingMonomialsDependOnTheOrder := by
  unfold LeadingMonomialsDependOnTheOrder
  decide +kernel

/-- Proves `MonicDependsOnTheOrder`. -/
public theorem monicDependsOnTheOrder : MonicDependsOnTheOrder := by
  unfold MonicDependsOnTheOrder
  decide +kernel

/-- Proves `NormalizationSortsAndAddsTerms`. -/
public theorem normalizationSortsAndAddsTerms : NormalizationSortsAndAddsTerms := by
  unfold NormalizationSortsAndAddsTerms
  decide +kernel

/-- Proves `CancellingTermsLeaveNoTerm`. -/
public theorem cancellingTermsLeaveNoTerm : CancellingTermsLeaveNoTerm := by
  unfold CancellingTermsLeaveNoTerm
  decide +kernel

/-- Proves `OneNormalizationForEveryCoefficientRing`. -/
public theorem oneNormalizationForEveryCoefficientRing : OneNormalizationForEveryCoefficientRing := by
  unfold OneNormalizationForEveryCoefficientRing
  exact ⟨by decide +kernel, five, new_five, by decide +kernel⟩

/-- Proves `TermsVanishingModuloTwoLeaveNoTerm`. -/
public theorem termsVanishingModuloTwoLeaveNoTerm : TermsVanishingModuloTwoLeaveNoTerm := by
  unfold TermsVanishingModuloTwoLeaveNoTerm
  exact ⟨two, new_two, by decide +kernel⟩

/-- Proves `SumsAndProductsOfBinomials`. -/
public theorem sumsAndProductsOfBinomials : SumsAndProductsOfBinomials := by
  unfold SumsAndProductsOfBinomials
  decide +kernel

/-- Proves `ZeroCoefficientsLeaveNoTerm`. -/
public theorem zeroCoefficientsLeaveNoTerm : ZeroCoefficientsLeaveNoTerm := by
  unfold ZeroCoefficientsLeaveNoTerm
  decide +kernel

/-- Proves `PowersOfABinomialAndOfZero`. -/
public theorem powersOfABinomialAndOfZero : PowersOfABinomialAndOfZero := by
  unfold PowersOfABinomialAndOfZero
  decide +kernel

/-- Proves `PowersModuloTwoAndPowersOfZero`. -/
public theorem powersModuloTwoAndPowersOfZero : PowersModuloTwoAndPowersOfZero := by
  unfold PowersModuloTwoAndPowersOfZero
  refine ⟨⟨two, new_two, by decide +kernel⟩, fun k hk => ?_⟩
  have hk0 : k ≠ 0 := by omega
  simp only [MultivariateRing.power, hk0, ↓reduceIte]
  generalize (binaryDigits k).tail = ds
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    rw [List.foldlM_cons]
    cases d <;> exact ih

/-- Proves `TermsExpandIntoPolynomials`. -/
public theorem termsExpandIntoPolynomials : TermsExpandIntoPolynomials := by
  unfold TermsExpandIntoPolynomials
  decide +kernel

/-- Proves `ForeignSymbolsAndNegativePowersFail`. -/
public theorem foreignSymbolsAndNegativePowersFail : ForeignSymbolsAndNegativePowersFail := by
  unfold ForeignSymbolsAndNegativePowersFail
  decide +kernel

/-- Proves `PolynomialsConvertBackToTerms`. -/
public theorem polynomialsConvertBackToTerms : PolynomialsConvertBackToTerms := by
  unfold PolynomialsConvertBackToTerms
  decide +kernel

/-- Proves `ConversionBuildsCanonicalTerms`. -/
public theorem conversionBuildsCanonicalTerms : ConversionBuildsCanonicalTerms := by
  unfold ConversionBuildsCanonicalTerms
  decide +kernel

end Kalyx.Proofs.Multivariate
