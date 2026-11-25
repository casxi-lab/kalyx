module

public import Kalyx.Statements.Polynomials

/-!
# Proofs of the statements about the ring operations

One theorem for each registered statement of `Kalyx.Statements.Polynomials`
about the ring operations and the derivative, whose type is exactly that
statement. They state that the operations return canonical polynomials that
denote the operations of Mathlib's `Polynomial`, and that the derivative
follows the product rule. Every proof is planned: each theorem is proved by
`sorry`, and the statements are registered with the state `planned` until
their proofs replace it.
-/

namespace Kalyx.Proofs.Polynomials

open Kalyx.Statements.Polynomials

/-- Proves `RingOperationsAreExact`; the proof is planned. -/
public theorem ringOperationsAreExact : RingOperationsAreExact := by
  sorry

/-- Proves `DerivativeFollowsTheProductRule`; the proof is planned. -/
public theorem derivativeFollowsTheProductRule : DerivativeFollowsTheProductRule := by
  sorry

end Kalyx.Proofs.Polynomials
