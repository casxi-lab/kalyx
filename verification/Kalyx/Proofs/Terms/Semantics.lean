module

public import Kalyx.Statements.Terms
import Kalyx.Proofs.Terms.Closure
import Kalyx.Proofs.Terms.Meaning

/-!
# Proofs of the statements about the meaning of terms

One theorem for each registered statement of `Kalyx.Statements.Terms` about
the meaning of the results of the constructors, whose type is exactly that
statement. The helper module `Kalyx.Proofs.Terms.Meaning`, which registers
nothing, proves it from the closure of the canonical forms
(`Kalyx.Proofs.Terms.Closure`), the bases of negative powers that the
constructors keep and the atomicity of calls (`Kalyx.Proofs.Terms.Bases`).
-/

namespace Kalyx.Proofs.Terms

open Kalyx.Statements.Terms

/-- Proves `ConstructorsKeepMeanings`. -/
public theorem constructorsKeepMeanings : ConstructorsKeepMeanings :=
  Meaning.constructorsKeepMeanings_of Closure.canonicalFormsAreClosedAndIdempotent_holds
    (Bases.constructorsKeepNegativeBases_of Closure.negationReadsOpposite) Bases.callsAreAtoms_holds

end Kalyx.Proofs.Terms
