module

public import Kalyx.Statements.Terms

/-!
# Proofs of the statements about the meaning of terms

One theorem for each registered statement of `Kalyx.Statements.Terms` about
the meaning of the results of the constructors, whose type is exactly that
statement. Every proof is planned: each theorem is proved by `sorry`, and the
statements are registered with the state `planned` until their proofs replace
it.
-/

namespace Kalyx.Proofs.Terms

open Kalyx.Statements.Terms

/-- Proves `ConstructorsKeepMeanings`; the proof is planned. -/
public theorem constructorsKeepMeanings : ConstructorsKeepMeanings := by
  sorry

end Kalyx.Proofs.Terms
