module

public import Kalyx.Statements.Multivariate

/-!
# Proofs of the statements about the examples

One theorem for each registered statement of `Kalyx.Statements.Multivariate`
about the positive and the negative example of each requirement of the
multivariate contract, whose type is exactly that statement. Every proof is
planned: each theorem is proved by `sorry`, and the statements are registered
with the state `planned` until their proofs replace it.
-/

namespace Kalyx.Proofs.Multivariate

open Kalyx.Statements.Multivariate

/-- Proves `ComparisonsUnderGrevlexAndABlockOrder`; the proof is planned. -/
public theorem comparisonsUnderGrevlexAndABlockOrder : ComparisonsUnderGrevlexAndABlockOrder := by
  sorry

/-- Proves `ComparisonsOfOtherOrdersDoNotHold`; the proof is planned. -/
public theorem comparisonsOfOtherOrdersDoNotHold : ComparisonsOfOtherOrdersDoNotHold := by
  sorry

/-- Proves `CanonicalFormOfThreeTerms`; the proof is planned. -/
public theorem canonicalFormOfThreeTerms : CanonicalFormOfThreeTerms := by
  sorry

/-- Proves `NonCanonicalTermLists`; the proof is planned. -/
public theorem nonCanonicalTermLists : NonCanonicalTermLists := by
  sorry

/-- Proves `RingsAreBuiltFromTheirData`; the proof is planned. -/
public theorem ringsAreBuiltFromTheirData : RingsAreBuiltFromTheirData := by
  sorry

/-- Proves `RepeatedNamesAndDifferentRings`; the proof is planned. -/
public theorem repeatedNamesAndDifferentRings : RepeatedNamesAndDifferentRings := by
  sorry

/-- Proves `LeadingMonomialsDependOnTheOrder`; the proof is planned. -/
public theorem leadingMonomialsDependOnTheOrder : LeadingMonomialsDependOnTheOrder := by
  sorry

/-- Proves `MonicDependsOnTheOrder`; the proof is planned. -/
public theorem monicDependsOnTheOrder : MonicDependsOnTheOrder := by
  sorry

/-- Proves `NormalizationSortsAndAddsTerms`; the proof is planned. -/
public theorem normalizationSortsAndAddsTerms : NormalizationSortsAndAddsTerms := by
  sorry

/-- Proves `CancellingTermsLeaveNoTerm`; the proof is planned. -/
public theorem cancellingTermsLeaveNoTerm : CancellingTermsLeaveNoTerm := by
  sorry

/-- Proves `OneNormalizationForEveryCoefficientRing`; the proof is planned. -/
public theorem oneNormalizationForEveryCoefficientRing : OneNormalizationForEveryCoefficientRing := by
  sorry

/-- Proves `TermsVanishingModuloTwoLeaveNoTerm`; the proof is planned. -/
public theorem termsVanishingModuloTwoLeaveNoTerm : TermsVanishingModuloTwoLeaveNoTerm := by
  sorry

/-- Proves `SumsAndProductsOfBinomials`; the proof is planned. -/
public theorem sumsAndProductsOfBinomials : SumsAndProductsOfBinomials := by
  sorry

/-- Proves `ZeroCoefficientsLeaveNoTerm`; the proof is planned. -/
public theorem zeroCoefficientsLeaveNoTerm : ZeroCoefficientsLeaveNoTerm := by
  sorry

/-- Proves `PowersOfABinomialAndOfZero`; the proof is planned. -/
public theorem powersOfABinomialAndOfZero : PowersOfABinomialAndOfZero := by
  sorry

/-- Proves `PowersModuloTwoAndPowersOfZero`; the proof is planned. -/
public theorem powersModuloTwoAndPowersOfZero : PowersModuloTwoAndPowersOfZero := by
  sorry

/-- Proves `TermsExpandIntoPolynomials`; the proof is planned. -/
public theorem termsExpandIntoPolynomials : TermsExpandIntoPolynomials := by
  sorry

/-- Proves `ForeignSymbolsAndNegativePowersFail`; the proof is planned. -/
public theorem foreignSymbolsAndNegativePowersFail : ForeignSymbolsAndNegativePowersFail := by
  sorry

/-- Proves `PolynomialsConvertBackToTerms`; the proof is planned. -/
public theorem polynomialsConvertBackToTerms : PolynomialsConvertBackToTerms := by
  sorry

/-- Proves `ConversionBuildsCanonicalTerms`; the proof is planned. -/
public theorem conversionBuildsCanonicalTerms : ConversionBuildsCanonicalTerms := by
  sorry

end Kalyx.Proofs.Multivariate
