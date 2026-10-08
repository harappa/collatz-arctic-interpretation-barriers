/-
The statements of the outputs of the parts of the proof for the system $\mathcal H$, and their assembly.
**The statements are frozen.**

The parts of the proof provide theorems proving the `Prop`s stated here, in `Gen/Spec.lean` and in `HModel/Defs.lean`. The assembly `htpdb_of_specs`
derives the five main theorems from them as hypotheses (pure logic, with no mathematical content). **Its purpose was to check in Lean,
before the parts were proved, that the interface statements fit together**; the final step (`HTPDB/Final.lean`) only applies the theorems of the parts and `HSPMain.hsp_holds` here.

* `SpecBridgeH` (`HTPDB/Main.lean`): the five main theorems from `AutoCoreH` (the $\mathcal H$ versions of `Main`, `DPMain`, `BZMain`).
* `SpecLeftUseH` (`HTPDB/LeftUse*.lean`): uses of the left-end rules (the $H$ version of `HLUMain.hLeftUse`; the boundary points are at steps $\mathsf a$).
* `SpecDynUseH` (`HTPDB/Uses.lean`): uses of the dynamic rules (the $H$ version of `FamilyUses`; `ff.` once per block, `ttt.` at least twice).
* `SpecQuadH` (`HTPDB/ARule*.lean`): quadratic uses of the carry rules $A$ (the $H$ version of `ARuleFive.aRule_quad`; carry families $Z_H$, $O_H$, $F_H$).
* The parts on uses take the interface statements of the model (`HModel.SpecHModel` etc.) as hypotheses, so they do not depend on their proofs.
-/
import CollatzProof.Arctic.Gen.Spec
import CollatzProof.Arctic.HTPDB.Statement
import CollatzProof.Arctic.HTPDB.DPStatement

namespace Collatz.Arctic.HTPDB

open Collatz.Arctic HModel

/-- Output of the bridge: the five main theorems from `AutoCoreH` (rule removal; dependency pairs, forward and reversed; below zero, forward and reversed). -/
def SpecBridgeH : Prop :=
  AutoCoreH → ArcticBarrierHT ∧ ArcticBarrierHDP ∧ ArcticBarrierHDPrev ∧ ArcticBarrierHBZ ∧
    ArcticBarrierHBZrev

/-- Output on the left-end rules: each of the 3 left-end rules is used at least `c k` times along the orbits of the family with probability close to 1. -/
def SpecLeftUseH : Prop :=
  SpecHModel → SpecHClass → SpecHBoundary →
    ∀ d ≤ 2, Gen.HUseR Hmap hR hSteps canDerivH (leftRule d)

/-- Output on the dynamic rules: uses of the 2 dynamic rules (an event of probability 1). -/
def SpecDynUseH : Prop :=
  SpecHModel → SpecHClass →
    Gen.HUseR Hmap hR hSteps canDerivH ffRule ∧ Gen.HUseR Hmap hR hSteps canDerivH tttRule

/-- Output on the carry rules: quadratic uses of the 6 carry rules $A$. -/
def SpecQuadH : Prop :=
  ∀ b d : ℕ, b < 2 → d ≤ 2 → Gen.QuadR Hmap HDom canDerivH (aRule b d)

/-- **Assembly (part 1)**: `AutoCoreH` from the outputs of the parts. The window frequency for $H$ comes from the swap argument (`e₂ = e₃ = 8`). -/
theorem autoCoreH_of_specs (hSP : HSP) (h1 : SpecHModel) (h2 : SpecHClass) (h3 : SpecHBoundary)
    (h4 : SpecHSwap) (g1 : Gen.SpecAutoRule) (g2 : Gen.SpecKeyOfSwap) (g3 : Gen.SpecWinOfKey)
    (g4 : Gen.SpecQuadRule) (u5 : SpecLeftUseH) (u6 : SpecDynUseH) (u6' : SpecQuadH) : AutoCoreH := by
  have hTW : Gen.HTerrasWinR hR :=
    g3 hR h1.R_lt h1.R_prefix (g2 hR h1.R_lt h1.R_prefix 8 8 le_rfl (by norm_num) h4)
  refine Gen.autoCoreG_of_rules (fun ρ hρ => ?_)
  rcases rulesHT_cases ρ hρ with ⟨b, d, hb, hd, rfl⟩ | rfl | rfl | ⟨d, hd, rfl⟩
  · exact g4 _ _ _ _ (u6' b d hb hd)
  · exact g1 (modelOf h1) canDerivH _ hSP hTW (u6 h1 h2).1
  · exact g1 (modelOf h1) canDerivH _ hSP hTW (u6 h1 h2).2
  · exact g1 (modelOf h1) canDerivH _ hSP hTW (u5 h1 h2 h3 d hd)

/-- **Assembly (part 2)**: the five main theorems from the outputs of the parts. -/
theorem htpdb_of_specs (hSP : HSP) (h1 : SpecHModel) (h2 : SpecHClass) (h3 : SpecHBoundary)
    (h4 : SpecHSwap) (g1 : Gen.SpecAutoRule) (g2 : Gen.SpecKeyOfSwap) (g3 : Gen.SpecWinOfKey)
    (g4 : Gen.SpecQuadRule) (u4 : SpecBridgeH) (u5 : SpecLeftUseH) (u6 : SpecDynUseH)
    (u6' : SpecQuadH) :
    ArcticBarrierHT ∧ ArcticBarrierHDP ∧ ArcticBarrierHDPrev ∧ ArcticBarrierHBZ ∧
      ArcticBarrierHBZrev :=
  u4 (autoCoreH_of_specs hSP h1 h2 h3 h4 g1 g2 g3 g4 u5 u6 u6')

end Collatz.Arctic.HTPDB
