/-
The barrier for rule removal for the reversed system of $R_H$ (unconditional; Theorem 3.1(ii), reversed form).
Applies `barrier_RHrev_of` of `RH/NonVacuity.lean` (transposition preserves `Weak`, `Strict`, `Fin00`) to `arcticBarrierRH` of
`RH/Final.lean`. For the system of the reversals of the 10 used rules, an interpretation satisfying `Fin00` that weakly orients all of them
strictly orients none of them.
-/
import CollatzProof.Arctic.RH.Final
import CollatzProof.Arctic.RH.NonVacuity

namespace Collatz.Arctic.RH

open Collatz.Arctic

/-- **Barrier for rule removal for the reversed system of $R_H$ (the reversals of the 10 used rules)** (unconditional). -/
theorem arcticBarrierRHrev : NonVacuity.BarrierFor (usedRH.map NonVacuity.revRule) :=
  NonVacuityRH.barrier_RHrev_of arcticBarrierRH

end Collatz.Arctic.RH
