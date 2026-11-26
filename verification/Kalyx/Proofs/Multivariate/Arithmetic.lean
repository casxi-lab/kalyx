module

public import Kalyx.Statements.Multivariate

/-!
# Proofs of the statements about the ring operations

One theorem for each registered statement of `Kalyx.Statements.Multivariate`
about the ring operations, whose type is exactly that statement. They state
that canonical forms are unique, and exist when the coefficients have
canonical forms, and that the ring operations and powers return canonical
polynomials that denote the operations of Mathlib's `MvPolynomial (Fin n)`.
Every proof is planned: each theorem is proved by `sorry`, and the statements
are registered with the state `planned` until their proofs replace it.
-/

namespace Kalyx.Proofs.Multivariate

open Kalyx.Statements.Multivariate

/-- Proves `RingOperationsAreExact`; the proof is planned. -/
public theorem ringOperationsAreExact : RingOperationsAreExact := by
  sorry

end Kalyx.Proofs.Multivariate
