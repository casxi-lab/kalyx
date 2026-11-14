module

public import Kalyx.Statements.Terms

/-!
# Proofs of the statements about the canonical forms

One theorem for each registered statement of `Kalyx.Statements.Terms` about
the canonical forms that the constructors return: their independence of the
order and the grouping of the operands, their closure and idempotence,
merging, the bases of negative powers, the faults of strict evaluation and the
atomicity of calls, whose type is exactly that statement. Every proof is
planned: each theorem is proved by `sorry`, and the statements are registered
with the state `planned` until their proofs replace it.
-/

namespace Kalyx.Proofs.Terms

open Kalyx.Statements.Terms

/-- Proves `SumsAndProductsIgnoreOrderAndGrouping`; the proof is planned. -/
public theorem sumsAndProductsIgnoreOrderAndGrouping : SumsAndProductsIgnoreOrderAndGrouping := by
  sorry

/-- Proves `CanonicalFormsAreClosedAndIdempotent`; the proof is planned. -/
public theorem canonicalFormsAreClosedAndIdempotent : CanonicalFormsAreClosedAndIdempotent := by
  sorry

/-- Proves `MergingAddsCoefficientsAndExponents`; the proof is planned. -/
public theorem mergingAddsCoefficientsAndExponents : MergingAddsCoefficientsAndExponents := by
  sorry

/-- Proves `ConstructorsKeepNegativeBases`; the proof is planned. -/
public theorem constructorsKeepNegativeBases : ConstructorsKeepNegativeBases := by
  sorry

/-- Proves `StrictEvaluationFaults`; the proof is planned. -/
public theorem strictEvaluationFaults : StrictEvaluationFaults := by
  sorry

/-- Proves `CallsAreAtoms`; the proof is planned. -/
public theorem callsAreAtoms : CallsAreAtoms := by
  sorry

end Kalyx.Proofs.Terms
