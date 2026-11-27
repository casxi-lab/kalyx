module

public import Kalyx.Statements.Multivariate
public import Kalyx.Proofs.Multivariate.Conversion

/-!
# Proofs of the statements about expansion and conversion back to terms

One theorem for each registered statement of `Kalyx.Statements.Multivariate`
about the expansion of terms and their conversion back, whose type is exactly
that statement. They state that the expansion of a term into a polynomial and
the conversion of a polynomial back to a canonical term keep the meaning of
terms.

The expansion is proved in `Kalyx.Proofs.Multivariate.Expansion`
(`expand_denote`): a term that expands meets only numbers, the variables of
the ring, sums, products and powers with nonnegative exponents, each of which
the ring operations take exactly. The conversion back is proved in
`Kalyx.Proofs.Multivariate.Conversion` (`conversionKeepsMeanings`) from the
canonical forms and the meaning of the constructors of the term core.
-/

namespace Kalyx.Proofs.Multivariate

open Kalyx.Statements.Multivariate

/-- Proves `ExpansionAndConversionKeepMeanings`. -/
public theorem expansionAndConversionKeepMeanings : ExpansionAndConversionKeepMeanings :=
  ⟨fun _ r I _ _ h => (Expansion.expand_denote r h I).2, Conversion.conversionKeepsMeanings⟩

end Kalyx.Proofs.Multivariate
