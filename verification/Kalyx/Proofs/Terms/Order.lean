module

public import Kalyx.Statements.Terms

/-!
# Proofs of the statements about the order of terms

One theorem for each registered statement of `Kalyx.Statements.Terms` about
the total order of terms and the comparison under `maxIntegerBits`, whose type
is exactly that statement. Every proof is planned: each theorem is proved by
`sorry`, and the statements are registered with the state `planned` until
their proofs replace it.
-/

namespace Kalyx.Proofs.Terms

open Kalyx.Statements.Terms

/-- Proves `TermOrderIsTotal`; the proof is planned. -/
public theorem termOrderIsTotal : TermOrderIsTotal := by
  sorry

/-- Proves `ComparisonUnderBitLimit`; the proof is planned. -/
public theorem comparisonUnderBitLimit : ComparisonUnderBitLimit := by
  sorry

end Kalyx.Proofs.Terms
