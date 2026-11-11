module

public import Kalyx.Proofs.Counter

namespace Kalyx.Proofs.Coerced

open Kalyx.Statements.Counter

/-- A proposition of the proofs. -/
@[expose] public def T : Prop := True

/-- A coercion of the proofs from `T` to the statement `W`. -/
public instance : Coe T W := ⟨fun _ => Kalyx.Proofs.Counter.t⟩

/-- A theorem of `T`, which `example : W := c` accepts through the coercion. -/
public theorem c : T := trivial

end Kalyx.Proofs.Coerced
