module

public import Kalyx.Statements.Terms

/-!
# Proofs of the statements about the examples

One theorem for each registered statement of `Kalyx.Statements.Terms` about
the positive and the negative example of each requirement of the terms
contract, whose type is exactly that statement. Every proof is planned: each
theorem is proved by `sorry`, and the statements are registered with the state
`planned` until their proofs replace it.
-/

namespace Kalyx.Proofs.Terms

open Kalyx.Statements.Terms

/-- Proves `ScaledCopiesOfOneSumMergeInEveryGrouping`; the proof is planned. -/
public theorem scaledCopiesOfOneSumMergeInEveryGrouping :
    ScaledCopiesOfOneSumMergeInEveryGrouping := by
  sorry

/-- Proves `OppositeSignsNeverMergeInAnyGrouping`; the proof is planned. -/
public theorem oppositeSignsNeverMergeInAnyGrouping : OppositeSignsNeverMergeInAnyGrouping := by
  sorry

/-- Proves `ContentThatCancelsLeavesNoProduct`; the proof is planned. -/
public theorem contentThatCancelsLeavesNoProduct : ContentThatCancelsLeavesNoProduct := by
  sorry

/-- Proves `NonCanonicalNodesFailTheShape`; the proof is planned. -/
public theorem nonCanonicalNodesFailTheShape : NonCanonicalNodesFailTheShape := by
  sorry

/-- Proves `SumsAndProductsSortTheirTerms`; the proof is planned. -/
public theorem sumsAndProductsSortTheirTerms : SumsAndProductsSortTheirTerms := by
  sorry

/-- Proves `UnsortedCoresAndTheByteOrder`; the proof is planned. -/
public theorem unsortedCoresAndTheByteOrder : UnsortedCoresAndTheByteOrder := by
  sorry

/-- Proves `LikeTermsAndCoefficientsMerge`; the proof is planned. -/
public theorem likeTermsAndCoefficientsMerge : LikeTermsAndCoefficientsMerge := by
  sorry

/-- Proves `OppositeSignsKeepTwoFactors`; the proof is planned. -/
public theorem oppositeSignsKeepTwoFactors : OppositeSignsKeepTwoFactors := by
  sorry

/-- Proves `ZeroAndOneDisappear`; the proof is planned. -/
public theorem zeroAndOneDisappear : ZeroAndOneDisappear := by
  sorry

/-- Proves `WitnessesKeepCancelledBases`; the proof is planned. -/
public theorem witnessesKeepCancelledBases : WitnessesKeepCancelledBases := by
  sorry

/-- Proves `PowersMergeAndDistribute`; the proof is planned. -/
public theorem powersMergeAndDistribute : PowersMergeAndDistribute := by
  sorry

/-- Proves `PowersThatWouldHideBasesStay`; the proof is planned. -/
public theorem powersThatWouldHideBasesStay : PowersThatWouldHideBasesStay := by
  sorry

/-- Proves `ZeroToTheZeroIsOne`; the proof is planned. -/
public theorem zeroToTheZeroIsOne : ZeroToTheZeroIsOne := by
  sorry

/-- Proves `StrictEvaluationFailures`; the proof is planned. -/
public theorem strictEvaluationFailures : StrictEvaluationFailures := by
  sorry

/-- Proves `LogicalBytesOfProducts`; the proof is planned. -/
public theorem logicalBytesOfProducts : LogicalBytesOfProducts := by
  sorry

/-- Proves `SharedSubtermsCountOncePerOccurrence`; the proof is planned. -/
public theorem sharedSubtermsCountOncePerOccurrence : SharedSubtermsCountOncePerOccurrence := by
  sorry

/-- Proves `DepthOfLeavesAndProducts`; the proof is planned. -/
public theorem depthOfLeavesAndProducts : DepthOfLeavesAndProducts := by
  sorry

/-- Proves `DepthIsNotSize`; the proof is planned. -/
public theorem depthIsNotSize : DepthIsNotSize := by
  sorry

/-- Proves `DisplayIsTheSameForEveryConstruction`; the proof is planned. -/
public theorem displayIsTheSameForEveryConstruction : DisplayIsTheSameForEveryConstruction := by
  sorry

/-- Proves `DisplayOfANegatedReciprocal`; the proof is planned. -/
public theorem displayOfANegatedReciprocal : DisplayOfANegatedReciprocal := by
  sorry

/-- Proves `SymbolNames`; the proof is planned. -/
public theorem symbolNames : SymbolNames := by
  sorry

/-- Proves `ReservedAndMalformedNames`; the proof is planned. -/
public theorem reservedAndMalformedNames : ReservedAndMalformedNames := by
  sorry

/-- Proves `EvalGivesTheCanonicalTerm`; the proof is planned. -/
public theorem evalGivesTheCanonicalTerm : EvalGivesTheCanonicalTerm := by
  sorry

/-- Proves `EvalOfFreeSymbolsFails`; the proof is planned. -/
public theorem evalOfFreeSymbolsFails : EvalOfFreeSymbolsFails := by
  sorry

/-- Proves `ConstantsMergeAndOrder`; the proof is planned. -/
public theorem constantsMergeAndOrder : ConstantsMergeAndOrder := by
  sorry

/-- Proves `ConstantsAreNotNegativeBases`; the proof is planned. -/
public theorem constantsAreNotNegativeBases : ConstantsAreNotNegativeBases := by
  sorry

/-- Proves `CallsMergeAsAtoms`; the proof is planned. -/
public theorem callsMergeAsAtoms : CallsMergeAsAtoms := by
  sorry

/-- Proves `CallsAreNotExpanded`; the proof is planned. -/
public theorem callsAreNotExpanded : CallsAreNotExpanded := by
  sorry

/-- Proves `ConditionsRankLastAndSelectBranches`; the proof is planned. -/
public theorem conditionsRankLastAndSelectBranches : ConditionsRankLastAndSelectBranches := by
  sorry

/-- Proves `ConditionsInValuePositionsFail`; the proof is planned. -/
public theorem conditionsInValuePositionsFail : ConditionsInValuePositionsFail := by
  sorry

end Kalyx.Proofs.Terms
