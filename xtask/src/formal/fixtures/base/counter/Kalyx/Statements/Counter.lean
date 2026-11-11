module

public import Kalyx.Spec.Counter

namespace Kalyx.Statements.Counter

open Kalyx.Spec.Counter

/-- A step increases the counter. -/
@[expose] public def S : Prop := ∀ n, n < step n

/-- A step does not decrease the counter. -/
@[expose] public def W : Prop := ∀ n, n ≤ step n

end Kalyx.Statements.Counter
