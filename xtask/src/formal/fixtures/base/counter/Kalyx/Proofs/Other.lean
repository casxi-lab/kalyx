module

public import Kalyx.Statements.Counter

namespace Kalyx.Proofs.Other

open Kalyx.Statements.Counter

/-- A statement defined in a proof module. -/
@[expose] public def P : Prop := True

public theorem u : S := by
  sorry

public theorem v : P := trivial

end Kalyx.Proofs.Other
