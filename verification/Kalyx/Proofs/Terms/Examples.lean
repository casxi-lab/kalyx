module

public import Kalyx.Statements.Terms

/-!
# Proofs of the statements about the examples

One theorem for each registered statement of `Kalyx.Statements.Terms` about
the positive and the negative example of each requirement of the terms
contract, whose type is exactly that statement.

The examples about given terms are decided by evaluation in the kernel
(`decide +kernel`). The positive canonical-form claim is split into its
decided shape (`Term.shapeOk`) and the validity of its constants, which holds
since that term holds no constant; a negated one is refuted by its decided
shape alone. The display examples compute their constructions and then unfold
the display, which reads no parameter; the `eval` examples split on the two
answers for closed formal nodes and decide each; the bytes of products and the
depth of leaves unfold the formulas of the bytes and of the depth.
-/

namespace Kalyx.Proofs.Terms

open Kalyx.Spec.Terms Kalyx.Statements.Terms

/-- Proves `ScaledCopiesOfOneSumMergeInEveryGrouping`. -/
public theorem scaledCopiesOfOneSumMergeInEveryGrouping :
    ScaledCopiesOfOneSumMergeInEveryGrouping := by
  unfold ScaledCopiesOfOneSumMergeInEveryGrouping
  decide +kernel

/-- Proves `OppositeSignsNeverMergeInAnyGrouping`. -/
public theorem oppositeSignsNeverMergeInAnyGrouping : OppositeSignsNeverMergeInAnyGrouping := by
  unfold OppositeSignsNeverMergeInAnyGrouping
  decide +kernel

/-- Proves `ContentThatCancelsLeavesNoProduct`. -/
public theorem contentThatCancelsLeavesNoProduct : ContentThatCancelsLeavesNoProduct := by
  unfold ContentThatCancelsLeavesNoProduct
  refine ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, ?_⟩, by decide +kernel⟩
  intro c hc
  simp [Term.nodes, Term.nodesPairs] at hc

/-- Proves `NonCanonicalNodesFailTheShape`. -/
public theorem nonCanonicalNodesFailTheShape : NonCanonicalNodesFailTheShape := by
  unfold NonCanonicalNodesFailTheShape
  exact ⟨fun h => absurd h.1 (by decide +kernel), fun h => absurd h.1 (by decide +kernel),
    fun h => absurd h.1 (by decide +kernel)⟩

/-- Proves `SumsAndProductsSortTheirTerms`. -/
public theorem sumsAndProductsSortTheirTerms : SumsAndProductsSortTheirTerms := by
  unfold SumsAndProductsSortTheirTerms
  decide +kernel

/-- Proves `UnsortedCoresAndTheByteOrder`. -/
public theorem unsortedCoresAndTheByteOrder : UnsortedCoresAndTheByteOrder := by
  unfold UnsortedCoresAndTheByteOrder
  exact ⟨fun h => absurd h.1 (by decide +kernel), by decide +kernel, by decide +kernel⟩

/-- Proves `LikeTermsAndCoefficientsMerge`. -/
public theorem likeTermsAndCoefficientsMerge : LikeTermsAndCoefficientsMerge := by
  unfold LikeTermsAndCoefficientsMerge
  decide +kernel

/-- Proves `OppositeSignsKeepTwoFactors`. -/
public theorem oppositeSignsKeepTwoFactors : OppositeSignsKeepTwoFactors := by
  unfold OppositeSignsKeepTwoFactors
  decide +kernel

/-- Proves `ZeroAndOneDisappear`. -/
public theorem zeroAndOneDisappear : ZeroAndOneDisappear := by
  unfold ZeroAndOneDisappear
  decide +kernel

/-- Proves `WitnessesKeepCancelledBases`. -/
public theorem witnessesKeepCancelledBases : WitnessesKeepCancelledBases := by
  unfold WitnessesKeepCancelledBases
  decide +kernel

/-- Proves `PowersMergeAndDistribute`. -/
public theorem powersMergeAndDistribute : PowersMergeAndDistribute := by
  unfold PowersMergeAndDistribute
  decide +kernel

/-- Proves `PowersThatWouldHideBasesStay`. -/
public theorem powersThatWouldHideBasesStay : PowersThatWouldHideBasesStay := by
  unfold PowersThatWouldHideBasesStay
  decide +kernel

/-- Proves `ZeroToTheZeroIsOne`. -/
public theorem zeroToTheZeroIsOne : ZeroToTheZeroIsOne := by
  unfold ZeroToTheZeroIsOne
  decide +kernel

/-- Proves `StrictEvaluationFailures`. -/
public theorem strictEvaluationFailures : StrictEvaluationFailures := by
  unfold StrictEvaluationFailures
  decide +kernel

/-- Proves `LogicalBytesOfProducts`. -/
public theorem logicalBytesOfProducts : LogicalBytesOfProducts := by
  refine ⟨fun p c name k hc _ => ?_, fun p a b => ?_⟩
  · simp [Term.bytes, Term.bytesList, ratBytes, hc]
    omega
  · simp [Term.bytes, Term.bytesList]

/-- Proves `SharedSubtermsCountOncePerOccurrence`. -/
public theorem sharedSubtermsCountOncePerOccurrence : SharedSubtermsCountOncePerOccurrence := by
  unfold SharedSubtermsCountOncePerOccurrence
  decide +kernel

/-- Proves `DepthOfLeavesAndProducts`. -/
public theorem depthOfLeavesAndProducts : DepthOfLeavesAndProducts :=
  ⟨fun _ => by simp [Term.depth], fun _ => by simp [Term.depth], by decide +kernel⟩

/-- Proves `DepthIsNotSize`. -/
public theorem depthIsNotSize : DepthIsNotSize := by
  unfold DepthIsNotSize
  decide +kernel

/-- Proves `DisplayIsTheSameForEveryConstruction`. -/
public theorem displayIsTheSameForEveryConstruction : DisplayIsTheSameForEveryConstruction := by
  unfold DisplayIsTheSameForEveryConstruction
  dsimp only
  intro p
  have h₁ : mkProduct Orders.sample defaultMaxExponent
      [.number 2, .sum 0 [(1, .symbol "x"), (1, .symbol "y")]] =
      .value (.sum 0 [(2, .symbol "x"), (2, .symbol "y")]) := by decide +kernel
  have h₂ : mkSum Orders.sample [.sum 0 [(1, .symbol "x"), (1, .symbol "y")],
      .sum 0 [(1, .symbol "x"), (1, .symbol "y")]] =
      .value (.sum 0 [(2, .symbol "x"), (2, .symbol "y")]) := by decide +kernel
  have h₃ : mkSum Orders.sample [.sum 0 [(2, .symbol "x"), (1, .symbol "y")], .symbol "y"] =
      .value (.sum 0 [(2, .symbol "x"), (2, .symbol "y")]) := by decide +kernel
  rw [h₁, h₂, h₃]
  simp only [Result.map, Term.display, Term.displayPairs]
  decide +kernel

/-- Proves `DisplayOfANegatedReciprocal`. -/
public theorem displayOfANegatedReciprocal : DisplayOfANegatedReciprocal := by
  unfold DisplayOfANegatedReciprocal
  dsimp only
  intro p
  have h : ((mkSubtract Orders.sample defaultMaxExponent (.number 1) (.symbol "x")).bind
      fun d => mkPower Orders.sample defaultMaxExponent d (-1)) =
      .value (.product (-1) [.power (.sum (-1) [(1, .symbol "x")]) (-1)]) := by decide +kernel
  rw [h]
  simp only [Result.map, Term.display, Term.displayList, Term.displayPairs]
  decide +kernel

/-- Proves `SymbolNames`. -/
public theorem symbolNames : SymbolNames := by
  unfold SymbolNames
  decide +kernel

/-- Proves `ReservedAndMalformedNames`. -/
public theorem reservedAndMalformedNames : ReservedAndMalformedNames := by
  unfold ReservedAndMalformedNames
  decide +kernel

/-- Proves `EvalGivesTheCanonicalTerm`. -/
public theorem evalGivesTheCanonicalTerm : EvalGivesTheCanonicalTerm := by
  unfold EvalGivesTheCanonicalTerm
  dsimp only
  intro cf
  cases cf <;> decide +kernel

/-- Proves `EvalOfFreeSymbolsFails`. -/
public theorem evalOfFreeSymbolsFails : EvalOfFreeSymbolsFails := by
  unfold EvalOfFreeSymbolsFails
  dsimp only
  intro cf
  cases cf <;> decide +kernel

/-- Proves `ConstantsMergeAndOrder`. -/
public theorem constantsMergeAndOrder : ConstantsMergeAndOrder := by
  unfold ConstantsMergeAndOrder
  decide +kernel

/-- Proves `ConstantsAreNotNegativeBases`. -/
public theorem constantsAreNotNegativeBases : ConstantsAreNotNegativeBases := by
  unfold ConstantsAreNotNegativeBases
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    fun h => absurd h.1 (by decide +kernel)⟩

/-- Proves `CallsMergeAsAtoms`. -/
public theorem callsMergeAsAtoms : CallsMergeAsAtoms := by
  unfold CallsMergeAsAtoms
  decide +kernel

/-- Proves `CallsAreNotExpanded`. -/
public theorem callsAreNotExpanded : CallsAreNotExpanded := by
  unfold CallsAreNotExpanded
  decide +kernel

/-- Proves `ConditionsRankLastAndSelectBranches`. -/
public theorem conditionsRankLastAndSelectBranches : ConditionsRankLastAndSelectBranches := by
  unfold ConditionsRankLastAndSelectBranches
  decide +kernel

/-- Proves `ConditionsInValuePositionsFail`. -/
public theorem conditionsInValuePositionsFail : ConditionsInValuePositionsFail := by
  unfold ConditionsInValuePositionsFail
  decide +kernel

end Kalyx.Proofs.Terms
