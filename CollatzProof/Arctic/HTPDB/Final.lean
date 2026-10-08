/-
The five main theorems on arctic barriers for the system $\mathcal H$ (collatz-T-5or7mod8 of the TPDB), without hypotheses.

The theorems of the seven parts of the proof and `HSPMain.hsp_holds` are applied to the frozen assembly `HTPDB.Spec.htpdb_of_specs`.
* the model of $H$ (`HModel/Terras*`, `Swap`): `specHModel`, `specHClass`, `specHBoundary`, `specHSwap`
* the generic assembly for one rule (`Gen/Family` to `Gen/Final`): `Gen.specAutoRule`
* the generic form of Theorem B.7 (`Gen/Key*`): `Gen.specKeyOfSwap` (with the swap constants `e₂ = e₃ = 8`)
* the generic form of Theorem B.8 (`Gen/HTW*`): `Gen.specWinOfKey`
* the bridge (`Gen/Sys*`, `HTPDB/Canon`, `DPCanon`, `Main`): `specBridgeH`
* uses of the left-end rules (`HTPDB/LeftUse*`): `specLeftUseH`
* uses of the dynamic and carry rules (`Gen/Quad`, `HTPDB/Uses`, `ARule*`): `Gen.specQuadRule`, `specDynUseH`, `specQuadH`
-/
import CollatzProof.Arctic.HTPDB.Spec
import CollatzProof.Arctic.HTPDB.Main
import CollatzProof.Arctic.HTPDB.LeftUseMain
import CollatzProof.Arctic.HTPDB.Uses
import CollatzProof.Arctic.HTPDB.ARuleFive
import CollatzProof.Arctic.HModel.Swap
import CollatzProof.Arctic.Gen.Final
import CollatzProof.Arctic.Gen.KeyMain4
import CollatzProof.Arctic.Gen.HTWFromKey
import CollatzProof.Arctic.Gen.Quad
import CollatzProof.Arctic.HSPMain

namespace Collatz.Arctic.HTPDB

open Collatz.Arctic

/-- The five main theorems (without hypotheses). -/
theorem htpdbBarriers :
    ArcticBarrierHT ∧ ArcticBarrierHDP ∧ ArcticBarrierHDPrev ∧ ArcticBarrierHBZ ∧
      ArcticBarrierHBZrev :=
  htpdb_of_specs hsp_holds HModel.specHModel HModel.specHClass HModel.specHBoundary HModel.specHSwap
    Gen.specAutoRule Gen.specKeyOfSwap Gen.specWinOfKey Gen.specQuadRule specBridgeH specLeftUseH
    specDynUseH specQuadH

/-- **Theorem 3.1** ($\mathcal H$, rule removal). -/
theorem arcticBarrierHT : ArcticBarrierHT := htpdbBarriers.1
/-- **Theorem 3.3** ($\mathcal H$, dependency pairs, forward). -/
theorem arcticBarrierHDP : ArcticBarrierHDP := htpdbBarriers.2.1
/-- **Theorem 3.3** ($\mathcal H$, dependency pairs, reversed). -/
theorem arcticBarrierHDPrev : ArcticBarrierHDPrev := htpdbBarriers.2.2.1
/-- **Theorem 3.4** ($\mathcal H$, below zero, forward). -/
theorem arcticBarrierHBZ : ArcticBarrierHBZ := htpdbBarriers.2.2.2.1
/-- **Theorem 3.4** ($\mathcal H$, below zero, reversed). -/
theorem arcticBarrierHBZrev : ArcticBarrierHBZrev := htpdbBarriers.2.2.2.2

end Collatz.Arctic.HTPDB
