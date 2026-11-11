module

public import Kalyx.Statements.Counter

namespace Kalyx.Proofs.Counter

open Kalyx.Statements.Counter Kalyx.Spec.Counter

/-- The weaker proposition. -/
public theorem t : W := by
  intro n
  unfold step
  omega

theorem helper : S := by
  intro n
  unfold step
  omega

public theorem s : S := helper

end Kalyx.Proofs.Counter
