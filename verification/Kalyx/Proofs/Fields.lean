module

public import Kalyx.Statements.Fields

/-!
# Proofs of the statements about the coefficient fields

One theorem for each registered statement of `Kalyx.Statements.Fields`, whose
type is exactly that statement. Every proof is planned: each theorem is
proved by `sorry`, and the statements are registered with the state
`planned` until their proofs replace it.
-/

namespace Kalyx.Proofs.Fields

open Kalyx.Statements.Fields

/-- Proves `RingAxioms`; the proof is planned. -/
public theorem ringAxioms : RingAxioms := by
  sorry

/-- Proves `FieldAxioms`; the proof is planned. -/
public theorem fieldAxioms : FieldAxioms := by
  sorry

/-- Proves `RingDivisionAndInverse`; the proof is planned. -/
public theorem ringDivisionAndInverse : RingDivisionAndInverse := by
  sorry

/-- Proves `ZeroTestsAreExact`; the proof is planned. -/
public theorem zeroTestsAreExact : ZeroTestsAreExact := by
  sorry

/-- Proves `CanonicalFormsAreUniqueAndComplete`; the proof is planned. -/
public theorem canonicalFormsAreUniqueAndComplete : CanonicalFormsAreUniqueAndComplete := by
  sorry

/-- Proves `MapsPreserveOperations`; the proof is planned. -/
public theorem mapsPreserveOperations : MapsPreserveOperations := by
  sorry

/-- Proves `ParallelPathsCommute`; the proof is planned. -/
public theorem parallelPathsCommute : ParallelPathsCommute := by
  sorry

/-- Proves `ReductionOutsideItsDomain`; the proof is planned. -/
public theorem reductionOutsideItsDomain : ReductionOutsideItsDomain := by
  sorry

/-- Proves `CanonicalFormExamples`; the proof is planned. -/
public theorem canonicalFormExamples : CanonicalFormExamples := by
  sorry

/-- Proves `NonCanonicalRepresentatives`; the proof is planned. -/
public theorem nonCanonicalRepresentatives : NonCanonicalRepresentatives := by
  sorry

/-- Proves `InverseExamples`; the proof is planned. -/
public theorem inverseExamples : InverseExamples := by
  sorry

/-- Proves `ZeroHasNoInverse`; the proof is planned. -/
public theorem zeroHasNoInverse : ZeroHasNoInverse := by
  sorry

/-- Proves `PowerExamples`; the proof is planned. -/
public theorem powerExamples : PowerExamples := by
  sorry

/-- Proves `PowerFailures`; the proof is planned. -/
public theorem powerFailures : PowerFailures := by
  sorry

/-- Proves `ZeroTestExamples`; the proof is planned. -/
public theorem zeroTestExamples : ZeroTestExamples := by
  sorry

/-- Proves `ZeroTestsOfHiddenZeros`; the proof is planned. -/
public theorem zeroTestsOfHiddenZeros : ZeroTestsOfHiddenZeros := by
  sorry

/-- Proves `EqualNumberFieldsCombine`; the proof is planned. -/
public theorem equalNumberFieldsCombine : EqualNumberFieldsCombine := by
  sorry

/-- Proves `DifferentNumberFieldsMismatch`; the proof is planned. -/
public theorem differentNumberFieldsMismatch : DifferentNumberFieldsMismatch := by
  sorry

/-- Proves `MapExamples`; the proof is planned. -/
public theorem mapExamples : MapExamples := by
  sorry

/-- Proves `ReductionOfOneSeventh`; the proof is planned. -/
public theorem reductionOfOneSeventh : ReductionOfOneSeventh := by
  sorry

/-- Proves `ProductWithinBitLimit`; the proof is planned. -/
public theorem productWithinBitLimit : ProductWithinBitLimit := by
  sorry

/-- Proves `ProductBeyondBitLimit`; the proof is planned. -/
public theorem productBeyondBitLimit : ProductBeyondBitLimit := by
  sorry

/-- Proves `IntegerDivisionExamples`; the proof is planned. -/
public theorem integerDivisionExamples : IntegerDivisionExamples := by
  sorry

/-- Proves `IntegerDivisionFailures`; the proof is planned. -/
public theorem integerDivisionFailures : IntegerDivisionFailures := by
  sorry

/-- Proves `ResidueInverseExamples`; the proof is planned. -/
public theorem residueInverseExamples : ResidueInverseExamples := by
  sorry

/-- Proves `ResidueFailures`; the proof is planned. -/
public theorem residueFailures : ResidueFailures := by
  sorry

/-- Proves `IntegerPathsAndResiduesAgree`; the proof is planned. -/
public theorem integerPathsAndResiduesAgree : IntegerPathsAndResiduesAgree := by
  sorry

/-- Proves `ResidueRingsAndPrimeFieldsDiffer`; the proof is planned. -/
public theorem residueRingsAndPrimeFieldsDiffer : ResidueRingsAndPrimeFieldsDiffer := by
  sorry

end Kalyx.Proofs.Fields
