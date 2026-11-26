module

public import Kalyx.Statements.Multivariate

/-!
# Proofs of the statements about expansion and conversion back to terms

One theorem for each registered statement of `Kalyx.Statements.Multivariate`
about the expansion of terms and their conversion back, whose type is exactly
that statement. They state that the expansion of a term into a polynomial and
the conversion of a polynomial back to a canonical term keep the meaning of
terms. Every proof is planned: each theorem is proved by `sorry`, and the
statements are registered with the state `planned` until their proofs replace
it.
-/

namespace Kalyx.Proofs.Multivariate

open Kalyx.Statements.Multivariate

/-- Proves `ExpansionAndConversionKeepMeanings`; the proof is planned. -/
public theorem expansionAndConversionKeepMeanings : ExpansionAndConversionKeepMeanings := by
  sorry

end Kalyx.Proofs.Multivariate
