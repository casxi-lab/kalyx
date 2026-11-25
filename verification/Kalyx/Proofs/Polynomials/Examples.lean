module

public import Kalyx.Statements.Polynomials
import Kalyx.Proofs.Fields
import Kalyx.Proofs.Polynomials.Canonical
import Kalyx.Proofs.Polynomials.Division

/-!
# Proofs of the statements about the examples

One theorem for each registered statement of `Kalyx.Statements.Polynomials`
about the positive and the negative example of each requirement of the
polynomials contract, whose type is exactly that statement.

The examples about given polynomials and terms are decided by evaluation in
the kernel (`decide +kernel`); an example over a prime field names the field
that the constructor builds from its modulus. Two examples are not closed
computations: the term lists that are not canonical are refuted by their
decided degrees and by a coefficient that denotes zero, and the product of
two zero divisors is the zero polynomial for every storage cost, since only
the zero polynomial is checked. The modular powers by a constant, of every
canonical polynomial to every exponent, follow from the statement that
modular powers are remainders (`ModularPowersAreRemainders`): the remainder
by the constant `3` is canonical and of degree below `0`, so it denotes zero
and is the zero polynomial; the power modulo zero is decided in the kernel.
-/

namespace Kalyx.Proofs.Polynomials

open Kalyx.Spec.Fields Kalyx.Spec.Polynomials Kalyx.Statements.Polynomials

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

/-- The prime field `𝔽_7`. -/
private def seven : PrimeField := ⟨7, by norm_num, by unfold WordModulus; norm_num⟩

/-- The constructor builds `𝔽_7` from `7`. -/
private theorem new_seven : PrimeField.new 7 = .built seven := by
  unfold PrimeField.new
  rw [dite_eq_left ⟨seven.prime, seven.word⟩]
  rfl

/-- Proves `SumsKeepOneTermOrNone`. -/
public theorem sumsKeepOneTermOrNone : SumsKeepOneTermOrNone := by
  unfold SumsKeepOneTermOrNone
  decide +kernel

/-- Proves `NonCanonicalTermLists`. -/
public theorem nonCanonicalTermLists : NonCanonicalTermLists := by
  unfold NonCanonicalTermLists
  refine ⟨fun h => absurd h.1 (by decide +kernel), fun h => ?_⟩
  exact (h.2 (Fraction.ofRat 0) (by decide +kernel)).2 (by decide +kernel)

/-- Proves `PowersOfZeroAndOfABinomial`. -/
public theorem powersOfZeroAndOfABinomial : PowersOfZeroAndOfABinomial := by
  unfold PowersOfZeroAndOfABinomial
  decide +kernel

/-- Proves `PowersCheckTheExponentFirst`. -/
public theorem powersCheckTheExponentFirst : PowersCheckTheExponentFirst := by
  unfold PowersCheckTheExponentFirst
  decide +kernel

/-- Proves `BinomialCoefficientsVanishModuloSeven`. -/
public theorem binomialCoefficientsVanishModuloSeven : BinomialCoefficientsVanishModuloSeven := by
  exact ⟨seven, new_seven, by decide +kernel⟩

/-- Proves `ZeroDivisorsLeaveNoTerm`. -/
public theorem zeroDivisorsLeaveNoTerm : ZeroDivisorsLeaveNoTerm := by
  intro μ
  rfl

/-- Proves `PowersAgreeUnderWiderLimits`. -/
public theorem powersAgreeUnderWiderLimits : PowersAgreeUnderWiderLimits := by
  unfold PowersAgreeUnderWiderLimits
  decide +kernel

/-- Proves `ExceededLimitsNameTheirField`. -/
public theorem exceededLimitsNameTheirField : ExceededLimitsNameTheirField := by
  unfold ExceededLimitsNameTheirField
  decide +kernel

/-- Proves `RingOfAVariableName`. -/
public theorem ringOfAVariableName : RingOfAVariableName := by
  unfold RingOfAVariableName
  decide +kernel

/-- Proves `ReservedAndMalformedVariables`. -/
public theorem reservedAndMalformedVariables : ReservedAndMalformedVariables := by
  unfold ReservedAndMalformedVariables
  decide +kernel

/-- Proves `DerivativeByANamedVariable`. -/
public theorem derivativeByANamedVariable : DerivativeByANamedVariable := by
  unfold DerivativeByANamedVariable
  decide +kernel

/-- Proves `TheVariableIsCheckedBeforeTheInput`. -/
public theorem theVariableIsCheckedBeforeTheInput : TheVariableIsCheckedBeforeTheInput := by
  unfold TheVariableIsCheckedBeforeTheInput
  decide +kernel

/-- Proves `StorageOfASparsePolynomial`. -/
public theorem storageOfASparsePolynomial : StorageOfASparsePolynomial := by
  unfold StorageOfASparsePolynomial
  decide +kernel

/-- Proves `NodesBoundTermsAndPartialSums`. -/
public theorem nodesBoundTermsAndPartialSums : NodesBoundTermsAndPartialSums := by
  unfold NodesBoundTermsAndPartialSums
  decide +kernel

/-- Proves `TermsExpandIntoPolynomials`. -/
public theorem termsExpandIntoPolynomials : TermsExpandIntoPolynomials := by
  unfold TermsExpandIntoPolynomials
  decide +kernel

/-- Proves `ForeignSymbolsAndNegativePowersFail`. -/
public theorem foreignSymbolsAndNegativePowersFail : ForeignSymbolsAndNegativePowersFail := by
  unfold ForeignSymbolsAndNegativePowersFail
  decide +kernel

/-- Proves `FailuresFollowTheWalk`. -/
public theorem failuresFollowTheWalk : FailuresFollowTheWalk := by
  unfold FailuresFollowTheWalk
  decide +kernel

/-- Proves `OnlyTheFirstFailureIsReported`. -/
public theorem onlyTheFirstFailureIsReported : OnlyTheFirstFailureIsReported := by
  unfold OnlyTheFirstFailureIsReported
  decide +kernel

/-- Proves `PolynomialsConvertBackToTerms`. -/
public theorem polynomialsConvertBackToTerms : PolynomialsConvertBackToTerms := by
  unfold PolynomialsConvertBackToTerms
  decide +kernel

/-- Proves `ConversionBuildsCanonicalTerms`. -/
public theorem conversionBuildsCanonicalTerms : ConversionBuildsCanonicalTerms := by
  unfold ConversionBuildsCanonicalTerms
  decide +kernel

/-- Proves `DerivativesOfPolynomialsAndTerms`. -/
public theorem derivativesOfPolynomialsAndTerms : DerivativesOfPolynomialsAndTerms := by
  unfold DerivativesOfPolynomialsAndTerms
  decide +kernel

/-- Proves `DerivativesThatVanishOrFail`. -/
public theorem derivativesThatVanishOrFail : DerivativesThatVanishOrFail := by
  unfold DerivativesThatVanishOrFail
  exact ⟨⟨seven, new_seven, by decide +kernel⟩, by decide +kernel⟩

/-- Proves `BinomialVectorExpands`. -/
public theorem binomialVectorExpands : BinomialVectorExpands := by
  unfold BinomialVectorExpands
  decide +kernel

/-- Proves `DegreeLimitVectorFails`. -/
public theorem degreeLimitVectorFails : DegreeLimitVectorFails := by
  unfold DegreeLimitVectorFails
  decide +kernel

/-- Proves `TermsWithinTheDepthExpand`. -/
public theorem termsWithinTheDepthExpand : TermsWithinTheDepthExpand := by
  unfold TermsWithinTheDepthExpand
  decide +kernel

/-- Proves `DeeperTermsFailAtTheEntry`. -/
public theorem deeperTermsFailAtTheEntry : DeeperTermsFailAtTheEntry := by
  unfold DeeperTermsFailAtTheEntry
  decide +kernel

/-- Proves `OneProductForEveryCoefficientRing`. -/
public theorem oneProductForEveryCoefficientRing : OneProductForEveryCoefficientRing := by
  unfold OneProductForEveryCoefficientRing
  exact ⟨by decide +kernel, five, new_five, by decide +kernel⟩

/-- Proves `CrossTermsVanishModuloTwo`. -/
public theorem crossTermsVanishModuloTwo : CrossTermsVanishModuloTwo := by
  exact ⟨two, new_two, by decide +kernel⟩

/-- Proves `BinomialCoefficientsOfAFourthPower`. -/
public theorem binomialCoefficientsOfAFourthPower : BinomialCoefficientsOfAFourthPower := by
  unfold BinomialCoefficientsOfAFourthPower
  decide +kernel

/-- Proves `ProductOfXAndXPlusOne`. -/
public theorem productOfXAndXPlusOne : ProductOfXAndXPlusOne := by
  unfold ProductOfXAndXPlusOne
  decide +kernel

/-- Proves `DivisionsWithRemainder`. -/
public theorem divisionsWithRemainder : DivisionsWithRemainder := by
  unfold DivisionsWithRemainder
  exact ⟨by decide +kernel, seven, new_seven, by decide +kernel⟩

/-- Proves `DivisionByZeroAndByAHigherDegree`. -/
public theorem divisionByZeroAndByAHigherDegree : DivisionByZeroAndByAHigherDegree := by
  unfold DivisionByZeroAndByAHigherDegree
  decide +kernel

/-- Proves `GcdsOfCommonFactors`. -/
public theorem gcdsOfCommonFactors : GcdsOfCommonFactors := by
  unfold GcdsOfCommonFactors
  decide +kernel

/-- Proves `GcdsWithZeroAndConstants`. -/
public theorem gcdsWithZeroAndConstants : GcdsWithZeroAndConstants := by
  unfold GcdsWithZeroAndConstants
  decide +kernel

/-- Proves `ExtendedGcdOfAMultiple`. -/
public theorem extendedGcdOfAMultiple : ExtendedGcdOfAMultiple := by
  unfold ExtendedGcdOfAMultiple
  decide +kernel

/-- Proves `ExtendedGcdsWithZero`. -/
public theorem extendedGcdsWithZero : ExtendedGcdsWithZero := by
  unfold ExtendedGcdsWithZero
  decide +kernel

/-- Proves `ModularPowerOfX`. -/
public theorem modularPowerOfX : ModularPowerOfX := by
  unfold ModularPowerOfX
  decide +kernel

/-- Proves `ModularPowersByZeroAndConstants`. -/
public theorem modularPowersByZeroAndConstants : ModularPowersByZeroAndConstants := by
  unfold ModularPowersByZeroAndConstants
  refine ⟨by decide +kernel, fun a k ha => ?_⟩
  have hF : ExactField Rationals.field Rationals.model :=
    ⟨⟨Kalyx.Proofs.Fields.ringAxioms.1, Kalyx.Proofs.Fields.zeroTestsAreExact.1⟩,
      Kalyx.Proofs.Fields.fieldAxioms.1⟩
  have hm : (ratPoly [(0, 3)]).Canonical Rationals.model ⟨⟩ := by
    rw [Kalyx.Proofs.Polynomials.Canonical.canonical_iff]
    refine ⟨by decide +kernel, fun x hx => ?_⟩
    simp only [ratPoly, List.map_cons, List.map_nil, List.mem_singleton] at hx
    subst hx
    refine ⟨?_, by decide +kernel⟩
    show Fraction.Reduced (Fraction.ofRat 3)
    unfold Fraction.Reduced
    decide +kernel
  obtain ⟨s, hs, hsc, hsd, -⟩ :=
    (modularPowersAreRemainders Rationals Fraction (fun _ => ℚ) Rationals.field Rationals.model
      hF).2 ⟨⟩ a k (ratPoly [(0, 3)]) ha hm (by decide +kernel)
  rw [Kalyx.Proofs.Polynomials.Canonical.degree_interpret _ _ hm] at hsd
  have hd : (s.interpret Rationals.model ⟨⟩).degree < 0 := by
    have h3 : (ratPoly [(0, 3)]).degree = some 0 := rfl
    rw [h3] at hsd
    exact hsd
  have h0 : s.interpret Rationals.model ⟨⟩ = 0 :=
    Polynomial.degree_eq_bot.1 (Nat.WithBot.lt_zero_iff.1 hd)
  rw [hs, (Kalyx.Proofs.Polynomials.Canonical.interpret_eq_zero_iff _ _ hsc).1 h0]

/-- Proves `EvaluationAtTwo`. -/
public theorem evaluationAtTwo : EvaluationAtTwo := by
  unfold EvaluationAtTwo
  decide +kernel

/-- Proves `EvaluationVanishesOnAllOfSeven`. -/
public theorem evaluationVanishesOnAllOfSeven : EvaluationVanishesOnAllOfSeven := by
  exact ⟨seven, new_seven, by decide +kernel, by decide +kernel⟩

/-- Proves `IntegerPolynomialsReduceModuloSeven`. -/
public theorem integerPolynomialsReduceModuloSeven : IntegerPolynomialsReduceModuloSeven := by
  exact ⟨seven, new_seven, by decide +kernel, by decide +kernel⟩

/-- Proves `ReductionOutsideTheDomain`. -/
public theorem reductionOutsideTheDomain : ReductionOutsideTheDomain := by
  exact ⟨seven, new_seven, by decide +kernel⟩

end Kalyx.Proofs.Polynomials
