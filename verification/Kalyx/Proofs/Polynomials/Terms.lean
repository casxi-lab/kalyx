module

public import Kalyx.Statements.Polynomials

/-!
# Proofs of the statements about expansion and conversion

One theorem for each registered statement of `Kalyx.Statements.Polynomials`
about the expansion of terms and their conversion back, whose type is exactly
that statement. They state that the expansion of a term into a polynomial and
the conversion of a polynomial back to a term keep the meaning of terms. Every
proof is planned: each theorem is proved by `sorry`, and the statements are
registered with the state `planned` until their proofs replace it.
-/

namespace Kalyx.Proofs.Polynomials

open Kalyx.Statements.Polynomials

/-- Proves `ExpansionKeepsMeanings`; the proof is planned. -/
public theorem expansionKeepsMeanings : ExpansionKeepsMeanings := by
  sorry

end Kalyx.Proofs.Polynomials
