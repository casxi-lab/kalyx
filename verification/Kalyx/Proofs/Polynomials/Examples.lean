module

public import Kalyx.Statements.Polynomials

/-!
# Proofs of the statements about the examples

One theorem for each registered statement of `Kalyx.Statements.Polynomials`
about the positive and the negative example of each requirement of the
polynomials contract, whose type is exactly that statement. Every proof is
planned: each theorem is proved by `sorry`, and the statements are registered
with the state `planned` until their proofs replace it.
-/

namespace Kalyx.Proofs.Polynomials

open Kalyx.Statements.Polynomials

/-- Proves `SumsKeepOneTermOrNone`; the proof is planned. -/
public theorem sumsKeepOneTermOrNone : SumsKeepOneTermOrNone := by
  sorry

/-- Proves `NonCanonicalTermLists`; the proof is planned. -/
public theorem nonCanonicalTermLists : NonCanonicalTermLists := by
  sorry

/-- Proves `PowersOfZeroAndOfABinomial`; the proof is planned. -/
public theorem powersOfZeroAndOfABinomial : PowersOfZeroAndOfABinomial := by
  sorry

/-- Proves `PowersCheckTheExponentFirst`; the proof is planned. -/
public theorem powersCheckTheExponentFirst : PowersCheckTheExponentFirst := by
  sorry

/-- Proves `BinomialCoefficientsVanishModuloSeven`; the proof is planned. -/
public theorem binomialCoefficientsVanishModuloSeven : BinomialCoefficientsVanishModuloSeven := by
  sorry

/-- Proves `ZeroDivisorsLeaveNoTerm`; the proof is planned. -/
public theorem zeroDivisorsLeaveNoTerm : ZeroDivisorsLeaveNoTerm := by
  sorry

/-- Proves `PowersAgreeUnderWiderLimits`; the proof is planned. -/
public theorem powersAgreeUnderWiderLimits : PowersAgreeUnderWiderLimits := by
  sorry

/-- Proves `ExceededLimitsNameTheirField`; the proof is planned. -/
public theorem exceededLimitsNameTheirField : ExceededLimitsNameTheirField := by
  sorry

/-- Proves `RingOfAVariableName`; the proof is planned. -/
public theorem ringOfAVariableName : RingOfAVariableName := by
  sorry

/-- Proves `ReservedAndMalformedVariables`; the proof is planned. -/
public theorem reservedAndMalformedVariables : ReservedAndMalformedVariables := by
  sorry

/-- Proves `DerivativeByANamedVariable`; the proof is planned. -/
public theorem derivativeByANamedVariable : DerivativeByANamedVariable := by
  sorry

/-- Proves `TheVariableIsCheckedBeforeTheInput`; the proof is planned. -/
public theorem theVariableIsCheckedBeforeTheInput : TheVariableIsCheckedBeforeTheInput := by
  sorry

/-- Proves `StorageOfASparsePolynomial`; the proof is planned. -/
public theorem storageOfASparsePolynomial : StorageOfASparsePolynomial := by
  sorry

/-- Proves `NodesBoundTermsAndPartialSums`; the proof is planned. -/
public theorem nodesBoundTermsAndPartialSums : NodesBoundTermsAndPartialSums := by
  sorry

/-- Proves `TermsExpandIntoPolynomials`; the proof is planned. -/
public theorem termsExpandIntoPolynomials : TermsExpandIntoPolynomials := by
  sorry

/-- Proves `ForeignSymbolsAndNegativePowersFail`; the proof is planned. -/
public theorem foreignSymbolsAndNegativePowersFail : ForeignSymbolsAndNegativePowersFail := by
  sorry

/-- Proves `FailuresFollowTheWalk`; the proof is planned. -/
public theorem failuresFollowTheWalk : FailuresFollowTheWalk := by
  sorry

/-- Proves `OnlyTheFirstFailureIsReported`; the proof is planned. -/
public theorem onlyTheFirstFailureIsReported : OnlyTheFirstFailureIsReported := by
  sorry

/-- Proves `PolynomialsConvertBackToTerms`; the proof is planned. -/
public theorem polynomialsConvertBackToTerms : PolynomialsConvertBackToTerms := by
  sorry

/-- Proves `ConversionBuildsCanonicalTerms`; the proof is planned. -/
public theorem conversionBuildsCanonicalTerms : ConversionBuildsCanonicalTerms := by
  sorry

/-- Proves `DerivativesOfPolynomialsAndTerms`; the proof is planned. -/
public theorem derivativesOfPolynomialsAndTerms : DerivativesOfPolynomialsAndTerms := by
  sorry

/-- Proves `DerivativesThatVanishOrFail`; the proof is planned. -/
public theorem derivativesThatVanishOrFail : DerivativesThatVanishOrFail := by
  sorry

/-- Proves `BinomialVectorExpands`; the proof is planned. -/
public theorem binomialVectorExpands : BinomialVectorExpands := by
  sorry

/-- Proves `DegreeLimitVectorFails`; the proof is planned. -/
public theorem degreeLimitVectorFails : DegreeLimitVectorFails := by
  sorry

/-- Proves `TermsWithinTheDepthExpand`; the proof is planned. -/
public theorem termsWithinTheDepthExpand : TermsWithinTheDepthExpand := by
  sorry

/-- Proves `DeeperTermsFailAtTheEntry`; the proof is planned. -/
public theorem deeperTermsFailAtTheEntry : DeeperTermsFailAtTheEntry := by
  sorry

/-- Proves `OneProductForEveryCoefficientRing`; the proof is planned. -/
public theorem oneProductForEveryCoefficientRing : OneProductForEveryCoefficientRing := by
  sorry

/-- Proves `CrossTermsVanishModuloTwo`; the proof is planned. -/
public theorem crossTermsVanishModuloTwo : CrossTermsVanishModuloTwo := by
  sorry

/-- Proves `BinomialCoefficientsOfAFourthPower`; the proof is planned. -/
public theorem binomialCoefficientsOfAFourthPower : BinomialCoefficientsOfAFourthPower := by
  sorry

/-- Proves `ProductOfXAndXPlusOne`; the proof is planned. -/
public theorem productOfXAndXPlusOne : ProductOfXAndXPlusOne := by
  sorry

/-- Proves `DivisionsWithRemainder`; the proof is planned. -/
public theorem divisionsWithRemainder : DivisionsWithRemainder := by
  sorry

/-- Proves `DivisionByZeroAndByAHigherDegree`; the proof is planned. -/
public theorem divisionByZeroAndByAHigherDegree : DivisionByZeroAndByAHigherDegree := by
  sorry

/-- Proves `GcdsOfCommonFactors`; the proof is planned. -/
public theorem gcdsOfCommonFactors : GcdsOfCommonFactors := by
  sorry

/-- Proves `GcdsWithZeroAndConstants`; the proof is planned. -/
public theorem gcdsWithZeroAndConstants : GcdsWithZeroAndConstants := by
  sorry

/-- Proves `ExtendedGcdOfAMultiple`; the proof is planned. -/
public theorem extendedGcdOfAMultiple : ExtendedGcdOfAMultiple := by
  sorry

/-- Proves `ExtendedGcdsWithZero`; the proof is planned. -/
public theorem extendedGcdsWithZero : ExtendedGcdsWithZero := by
  sorry

/-- Proves `ModularPowerOfX`; the proof is planned. -/
public theorem modularPowerOfX : ModularPowerOfX := by
  sorry

/-- Proves `ModularPowersByZeroAndConstants`; the proof is planned. -/
public theorem modularPowersByZeroAndConstants : ModularPowersByZeroAndConstants := by
  sorry

/-- Proves `EvaluationAtTwo`; the proof is planned. -/
public theorem evaluationAtTwo : EvaluationAtTwo := by
  sorry

/-- Proves `EvaluationVanishesOnAllOfSeven`; the proof is planned. -/
public theorem evaluationVanishesOnAllOfSeven : EvaluationVanishesOnAllOfSeven := by
  sorry

/-- Proves `IntegerPolynomialsReduceModuloSeven`; the proof is planned. -/
public theorem integerPolynomialsReduceModuloSeven : IntegerPolynomialsReduceModuloSeven := by
  sorry

/-- Proves `ReductionOutsideTheDomain`; the proof is planned. -/
public theorem reductionOutsideTheDomain : ReductionOutsideTheDomain := by
  sorry

end Kalyx.Proofs.Polynomials
