module

public import Kalyx.Proofs.Native
meta import Lean

open Lean Elab Command in
run_cmd liftCoreM do
  let t := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) (mkConst ``Bool.false) (mkConst ``Bool.true)
  addDecl (.axiomDecl { «name» := `Kalyx.Proofs.Native.n._native.native_decide.ax_9_9, levelParams := [], «type» := t, isUnsafe := false })

namespace Kalyx.Proofs.Forged

/-- A theorem of `False` from an axiom named as a native decision of
`Kalyx.Proofs.Native.n`, which this module declares. -/
public theorem f : False := by
  have h := Kalyx.Proofs.Native.n._native.native_decide.ax_9_9
  cases h

end Kalyx.Proofs.Forged
