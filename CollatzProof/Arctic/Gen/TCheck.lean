/-
Check of the generic layer (`Gen/`): applying it to the model `tModel` of $T$, we rederive the frozen statements for $T$ (`HKeyTop`, `HTerrasWin`) and
`AutoRuleG` for the left-end rules and the carry rules of $T$.
Not in the closure of the main theorem for $T$ (`Summary.lean`).
-/
import CollatzProof.Arctic.Gen.Final
import CollatzProof.Arctic.Gen.KeyMain4
import CollatzProof.Arctic.Gen.HTWFromKey
import CollatzProof.Arctic.Gen.Quad
import CollatzProof.Arctic.Gen.ModelT
import CollatzProof.Arctic.HSPMain
import CollatzProof.Arctic.HLUMain

namespace Collatz.Arctic.Gen.TCheck

open Collatz.Arctic Gen

/-- From the generalization of the swap argument, the frozen `HKeyTop` (swap exponents `ν₂ = 9`, `ν₃ = 7`). -/
theorem hKeyTop_gen : HKeyTop :=
  hKeyTop_iff.mpr (hKeyTopR_of_swap tModel.R tModel.R_lt tModel.R_prefix 9 7 (by norm_num) tModel_swap)

/-- From the generalization of the window frequencies, the frozen `HTerrasWin`. -/
theorem hTerrasWin_gen : HTerrasWin :=
  hTerrasWin_iff.mpr (hTerrasWinR_of_key tModel.R tModel.R_lt tModel.R_prefix (hKeyTop_iff.mp hKeyTop_gen))

/-- From the generalization of the assembly, `AutoRuleG` for the left-end rules of $T$. -/
theorem autoRule_left_gen (d : ℕ) (hd : d ≤ 2) : AutoRuleG T (fun n => 2 ≤ n) canDeriv (leftRule d) :=
  specAutoRule tModel canDeriv (leftRule d) hsp_holds (hTerrasWin_iff.mp hTerrasWin_gen)
    (hUseR_of_hLeftUse hLeftUse d hd)

/-- From `Gen/Quad`, `AutoRuleG` for the carry rules of $T$. -/
theorem autoRule_A_gen (b d : ℕ) (hb : b < 2) (hd : d ≤ 2) :
    AutoRuleG T (fun n => 2 ≤ n) canDeriv (aRule b d) :=
  specQuadRule T (fun n => 2 ≤ n) canDeriv (aRule b d) (tModel_quad b d hb hd)

end Collatz.Arctic.Gen.TCheck
