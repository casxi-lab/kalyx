module

namespace Kalyx.Proofs.Native

/-- A native decision. -/
public theorem n : 2 ^ 10 = 1024 := by native_decide

end Kalyx.Proofs.Native
