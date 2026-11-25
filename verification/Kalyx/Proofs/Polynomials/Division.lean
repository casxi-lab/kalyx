module

public import Kalyx.Statements.Polynomials

/-!
# Proofs of the statements about division and the GCDs

One theorem for each registered statement of `Kalyx.Statements.Polynomials`
about the shared algorithms over a coefficient field, whose type is exactly
that statement. They state that division with remainder, the monic GCD and the
extended GCD with the cofactors of lowest degree are determined by their
defining conditions, and that modular powers are remainders. Every proof is
planned: each theorem is proved by `sorry`, and the statements are registered
with the state `planned` until their proofs replace it.
-/

namespace Kalyx.Proofs.Polynomials

open Kalyx.Statements.Polynomials

/-- Proves `DivisionWithRemainderIsUnique`; the proof is planned. -/
public theorem divisionWithRemainderIsUnique : DivisionWithRemainderIsUnique := by
  sorry

/-- Proves `MonicGcdIsUnique`; the proof is planned. -/
public theorem monicGcdIsUnique : MonicGcdIsUnique := by
  sorry

/-- Proves `ExtendedGcdHasLowestCofactors`; the proof is planned. -/
public theorem extendedGcdHasLowestCofactors : ExtendedGcdHasLowestCofactors := by
  sorry

/-- Proves `ModularPowersAreRemainders`; the proof is planned. -/
public theorem modularPowersAreRemainders : ModularPowersAreRemainders := by
  sorry

end Kalyx.Proofs.Polynomials
