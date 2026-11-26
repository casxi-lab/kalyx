module

public import Kalyx.Statements.Multivariate

/-!
# Proofs of the statements about the monomial orders

One theorem for each registered statement of `Kalyx.Statements.Multivariate`
about the monomial orders, whose type is exactly that statement. They state
that each monomial order is a strict total order with which its computable
comparison agrees, compatible with the product of monomials and well founded,
with the constant monomial least, that a block order eliminates its first
block, and that each order is the strict order of a monomial order of Mathlib.
Every proof is planned: each theorem is proved by `sorry`, and the statements
are registered with the state `planned` until their proofs replace it.
-/

namespace Kalyx.Proofs.Multivariate

open Kalyx.Statements.Multivariate

/-- Proves `MonomialOrdersAreStrictTotalOrders`; the proof is planned. -/
public theorem monomialOrdersAreStrictTotalOrders : MonomialOrdersAreStrictTotalOrders := by
  sorry

/-- Proves `MonomialOrdersRespectProducts`; the proof is planned. -/
public theorem monomialOrdersRespectProducts : MonomialOrdersRespectProducts := by
  sorry

/-- Proves `MonomialOrdersAreWellFounded`; the proof is planned. -/
public theorem monomialOrdersAreWellFounded : MonomialOrdersAreWellFounded := by
  sorry

/-- Proves `TheConstantMonomialIsLeast`; the proof is planned. -/
public theorem theConstantMonomialIsLeast : TheConstantMonomialIsLeast := by
  sorry

/-- Proves `BlockOrdersEliminateTheirFirstBlock`; the proof is planned. -/
public theorem blockOrdersEliminateTheirFirstBlock : BlockOrdersEliminateTheirFirstBlock := by
  sorry

/-- Proves `MonomialOrdersAreThoseOfMathlib`; the proof is planned. -/
public theorem monomialOrdersAreThoseOfMathlib : MonomialOrdersAreThoseOfMathlib := by
  sorry

end Kalyx.Proofs.Multivariate
