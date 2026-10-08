/-
Summary of the formalization of the arctic barrier for 𝒯. The main theorems follow from three hypotheses of finite form.

* Hypotheses (`CoreHyp.lean`): `HSP` (the finite form, Corollary B.4; random max-plus products), `HTerrasWin` (Theorem B.8;
  window frequencies in the model of `T`), `HLeftUse` (Proposition 6.7: uses of the left-end rules; frequencies of the top windows of the block boundary points).
  **`HLeftUse` is proved** (`HLUMain.hLeftUse`; Proposition B.9). So the hypotheses of the main theorems reduce to `HSP` and `HTerrasWin`
  (`barrier_ST'` and the others below). `HTerrasWin` follows from `HKeyTop` (Theorem B.7) (`HTWFromKey.hTerrasWin_of_key`),
  and **`HSP` is proved** (`HSPMain.hsp_holds`; Corollary B.4, from Theorem B.3). So the only hypothesis left is `HKeyTop` (`barrier_ST_key` and the others below).
  **`HKeyTop` is proved as well** (`KeyFinal.hKeyTop`; Theorem B.7, the swap argument of Appendix B.2). Hence **the main theorems hold without hypotheses** (`arcticBarrierST`
  and the others at the end).
* The common hypothesis `AutoCore` (`AutoStatement.lean`) follows from the three hypotheses (`CoreFinal.autoCore_of_hyps`; Theorem 6.8).
* Main theorems: rule removal (Theorem 3.1, `ArcticBarrierST`), reduction pairs for dependency pairs (Theorem 3.3, for the system and its reversal),
  below zero (Theorem 3.4, for the system and its reversal).
-/
import CollatzProof.Arctic.CoreFinal
import CollatzProof.Arctic.AutoBridge
import CollatzProof.Arctic.DPMain
import CollatzProof.Arctic.BZMain
import CollatzProof.Arctic.HLUMain
import CollatzProof.Arctic.HTWFromKey
import CollatzProof.Arctic.HSPMain
import CollatzProof.Arctic.KeyFinal

namespace Collatz.Arctic

/-- Theorem 3.1 (𝒯, rule removal). -/
theorem barrier_ST (h₁ : HSP) (h₂ : HTerrasWin) (h₃ : HLeftUse) : ArcticBarrierST :=
  arctic_barrier_ST (valueCore_of_autoCore (autoCore_of_hyps h₁ h₂ h₃))

/-- Theorem 3.3 (𝒯, dependency pairs). -/
theorem barrier_DP (h₁ : HSP) (h₂ : HTerrasWin) (h₃ : HLeftUse) : ArcticBarrierDP :=
  arctic_barrier_DP (autoCore_of_hyps h₁ h₂ h₃)

/-- Theorem 3.3 (the reversal of 𝒯, dependency pairs). -/
theorem barrier_DPrev (h₁ : HSP) (h₂ : HTerrasWin) (h₃ : HLeftUse) : ArcticBarrierDPrev :=
  arctic_barrier_DPrev (autoCore_of_hyps h₁ h₂ h₃)

/-- Theorem 3.4 (𝒯, below zero). -/
theorem barrier_BZ (h₁ : HSP) (h₂ : HTerrasWin) (h₃ : HLeftUse) : ArcticBarrierBZ :=
  arctic_barrier_BZ (autoCore_of_hyps h₁ h₂ h₃)

/-- Theorem 3.4 (the reversal of 𝒯, below zero). -/
theorem barrier_BZrev (h₁ : HSP) (h₂ : HTerrasWin) (h₃ : HLeftUse) : ArcticBarrierBZrev :=
  arctic_barrier_BZrev (autoCore_of_hyps h₁ h₂ h₃)

/-! ## The forms after proving `HLeftUse` (hypotheses `HSP` and `HTerrasWin` only) -/

theorem barrier_ST' (h₁ : HSP) (h₂ : HTerrasWin) : ArcticBarrierST := barrier_ST h₁ h₂ hLeftUse
theorem barrier_DP' (h₁ : HSP) (h₂ : HTerrasWin) : ArcticBarrierDP := barrier_DP h₁ h₂ hLeftUse
theorem barrier_DPrev' (h₁ : HSP) (h₂ : HTerrasWin) : ArcticBarrierDPrev := barrier_DPrev h₁ h₂ hLeftUse
theorem barrier_BZ' (h₁ : HSP) (h₂ : HTerrasWin) : ArcticBarrierBZ := barrier_BZ h₁ h₂ hLeftUse
theorem barrier_BZrev' (h₁ : HSP) (h₂ : HTerrasWin) : ArcticBarrierBZrev := barrier_BZrev h₁ h₂ hLeftUse

/-! ## The forms after deriving `HTerrasWin` from `HKeyTop` (hypotheses `HSP` and `HKeyTop` only) -/

theorem barrier_ST'' (h₁ : HSP) (h₂ : HKeyTop) : ArcticBarrierST := barrier_ST' h₁ (hTerrasWin_of_key h₂)
theorem barrier_DP'' (h₁ : HSP) (h₂ : HKeyTop) : ArcticBarrierDP := barrier_DP' h₁ (hTerrasWin_of_key h₂)
theorem barrier_DPrev'' (h₁ : HSP) (h₂ : HKeyTop) : ArcticBarrierDPrev :=
  barrier_DPrev' h₁ (hTerrasWin_of_key h₂)
theorem barrier_BZ'' (h₁ : HSP) (h₂ : HKeyTop) : ArcticBarrierBZ := barrier_BZ' h₁ (hTerrasWin_of_key h₂)
theorem barrier_BZrev'' (h₁ : HSP) (h₂ : HKeyTop) : ArcticBarrierBZrev :=
  barrier_BZrev' h₁ (hTerrasWin_of_key h₂)

/-! ## The forms after proving `HSP` (hypothesis `HKeyTop` only; `HSPMain.hsp_holds`) -/

theorem barrier_ST_key (h : HKeyTop) : ArcticBarrierST := barrier_ST'' hsp_holds h
theorem barrier_DP_key (h : HKeyTop) : ArcticBarrierDP := barrier_DP'' hsp_holds h
theorem barrier_DPrev_key (h : HKeyTop) : ArcticBarrierDPrev := barrier_DPrev'' hsp_holds h
theorem barrier_BZ_key (h : HKeyTop) : ArcticBarrierBZ := barrier_BZ'' hsp_holds h
theorem barrier_BZrev_key (h : HKeyTop) : ArcticBarrierBZrev := barrier_BZrev'' hsp_holds h

/-! ## The forms without hypotheses (after proving `HSP`, `HTerrasWin` and `HLeftUse`) -/

/-- **Theorem 3.1** (𝒯, rule removal). -/
theorem arcticBarrierST : ArcticBarrierST := barrier_ST_key hKeyTop
/-- **Theorem 3.3** (𝒯, dependency pairs). -/
theorem arcticBarrierDP : ArcticBarrierDP := barrier_DP_key hKeyTop
/-- **Theorem 3.3** (the reversal of 𝒯, dependency pairs). -/
theorem arcticBarrierDPrev : ArcticBarrierDPrev := barrier_DPrev_key hKeyTop
/-- **Theorem 3.4** (𝒯, below zero). -/
theorem arcticBarrierBZ : ArcticBarrierBZ := barrier_BZ_key hKeyTop
/-- **Theorem 3.4** (the reversal of 𝒯, below zero). -/
theorem arcticBarrierBZrev : ArcticBarrierBZrev := barrier_BZrev_key hKeyTop

end Collatz.Arctic
