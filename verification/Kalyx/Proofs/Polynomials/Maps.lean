module

public import Kalyx.Statements.Polynomials

/-!
# Proofs of the statements about evaluation and maps

One theorem for each registered statement of `Kalyx.Statements.Polynomials`
about evaluation and the maps of polynomials, whose type is exactly that
statement. They state that evaluation is a homomorphism and that a map acts on
each coefficient. Every proof is planned: each theorem is proved by `sorry`,
and the statements are registered with the state `planned` until their proofs
replace it.
-/

namespace Kalyx.Proofs.Polynomials

open Kalyx.Statements.Polynomials

/-- Proves `EvaluationIsAHomomorphism`; the proof is planned. -/
public theorem evaluationIsAHomomorphism : EvaluationIsAHomomorphism := by
  sorry

/-- Proves `MapsActOnEachCoefficient`; the proof is planned. -/
public theorem mapsActOnEachCoefficient : MapsActOnEachCoefficient := by
  sorry

end Kalyx.Proofs.Polynomials
