module

public import Kalyx.Statements.Multivariate

/-!
# Proofs of the statements about the form of the polynomials

One theorem for each registered statement of `Kalyx.Statements.Multivariate`
about the form of the polynomials, whose type is exactly that statement. They
state that the leading term, the total degree and the monic test are those of
Mathlib under every monomial order of Mathlib that agrees with the order of
the ring, and that normalization gives the canonical form of the sum of its
terms, whatever their order. Every proof is planned: each theorem is proved by
`sorry`, and the statements are registered with the state `planned` until
their proofs replace it.
-/

namespace Kalyx.Proofs.Multivariate

open Kalyx.Statements.Multivariate

/-- Proves `LeadingTermsAreThoseOfMathlib`; the proof is planned. -/
public theorem leadingTermsAreThoseOfMathlib : LeadingTermsAreThoseOfMathlib := by
  sorry

/-- Proves `NormalizationGivesCanonicalForms`; the proof is planned. -/
public theorem normalizationGivesCanonicalForms : NormalizationGivesCanonicalForms := by
  sorry

end Kalyx.Proofs.Multivariate
