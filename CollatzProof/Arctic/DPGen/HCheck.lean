/-
Lean foundation of Section 8 (Section 8.1): a check. The four dependency pair theorems for $\mathcal H$ (forward and reversed, `𝔸_ℕ` and
below zero) are re-derived from the **family form** of the general lemma (`Sim.simulation_family_arc(Z)`). This file is not in the closure of the
main theorems for $\mathcal H$ (`HTPDB/Final.lean`).

`HTPDB/Main.lean` derived them from `AutoCoreH` (the form with the slope hypothesis on the whole domain `HDom`). Here (a) is used **only at points
of family orbits** (carrying `HTPDB.DPCanon.dcanDerivH`, `dcanDerivH_rev` over by `STConv.gdchain_of_dchain`), and (c) is
obtained by Corollary 8.1 (`Family.autoUseG_family`) from the window frequencies `hTerrasWinR_H` of $H$ and the numbers of uses along the family:
the left-end rules (`specLeftUseH`) in the forward direction, the dynamic rules (`specDynUseH`) in the reversed direction. This checks that the form that does not use the values at points outside the family
(Corollary 8.1) also works in the reversed direction (Theorem 8.3 needs the corollary for labelled reversed systems; here the system is the unlabelled
$\mathcal H$, and the application to labelled systems is outside the scope of this file).
-/
import CollatzProof.Arctic.DPGen.STCheck
import CollatzProof.Arctic.HTPDB.DPCanon

namespace Collatz.Arctic.DPGen

open Collatz.Arctic Collatz.Arctic.Gen Collatz.Arctic.HModel Collatz.Arctic.HTPDB Matrix

/-! ## Forward direction (uses of the left-end rules) -/

theorem rootPB_notin_usableHT {d' : ℕ} (hd' : d' ≤ 2) : leftRule d' ∉ usableHT := by
  interval_cases d' <;> decide

/-- The numbers of uses of the left-end rules along the family (in the form `HUseC`). -/
theorem hUseC_left_H {d' : ℕ} (hd' : d' ≤ 2) :
    HUseC Hmap hR hSteps (fun n => (canDerivH n).count (leftRule d')) :=
  (hUseR_iff_use _ _ _ _ _).mp (specLeftUseH specHModel specHClass specHBoundary d' hd')

/-- Condition (a), forward: carry over the canonical dependency pair chains at points of family orbits (points of `HDom`). -/
theorem fwd_chain_H {d' : ℕ} (hd' : d' ≤ 2) (n : ℕ) (hn : famDom (modelOf specHModel) n) :
    ∃ es, GDChain (usableHT.map plainR) (rootPB.map (dpR Letter.lft)) es (encFwd n)
      (encFwd (Hmap n)) ∧
      (canDerivH n).count (leftRule d') ≤ es.count (GLabel.root (dpR Letter.lft (leftRule d'))) :=
  gdchain_of_dchain Letter.lft (rootPB_notin_usableHT hd') (dcanDerivH n hn.2)

/-- **Theorem 3.3 ($\mathcal H$, forward, `𝔸_ℕ`) from the general lemma (family form)**. -/
theorem arcticBarrierHDP_gen : ArcticBarrierHDP := by
  intro d hd J hSF hU hP π hπ hs
  rw [pairsPB_eq] at hπ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hπ
  obtain ⟨d', hd', rfl⟩ := rootPB_cases hσ
  obtain ⟨hU', hP'⟩ := weak_lift hd J Letter.lft pairsPB_eq hU hP
  refine simulation_family_arc (modelOf specHModel) hTerrasWinR_H (hUseC_left_H hd') encFwd
    (usableHT.map plainR) (rootPB.map (dpR Letter.lft)) (dpR Letter.lft (leftRule d'))
    (fwd_chain_H hd') hd (liftJ J) ?_ ?_ hU' hP' ((strictTop_ofDR hd J _).mpr hs)
  · exact ⟨d + 1, fun j => hom (J (DLetter.mark Letter.lft)) (c0 hd) j, homL J,
      homL J Letter.rgt *ᵥ xs hd, fun n => by rw [encFwd, gV_eq_Vw, Vw_fwd_eq]; rfl⟩
  · intro n
    rw [encFwd, gV_eq_Vw]
    exact Vw_ne_zero hd J lettersPB hSF Letter.lft (by decide) _ (fwd_letters n)

/-- **Theorem 3.4 ($\mathcal H$, forward, below zero) from the general lemma (family form)**. -/
theorem arcticBarrierHBZ_gen : ArcticBarrierHBZ := by
  intro d hd J hAP hU hP π hπ hs
  rw [pairsPB_eq] at hπ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hπ
  obtain ⟨d', hd', rfl⟩ := rootPB_cases hσ
  obtain ⟨hU', hP'⟩ := weak_lift hd J Letter.lft pairsPB_eq hU hP
  refine simulation_family_arcZ (modelOf specHModel) hTerrasWinR_H (hUseC_left_H hd') encFwd
    (usableHT.map plainR) (rootPB.map (dpR Letter.lft)) (dpR Letter.lft (leftRule d'))
    (fwd_chain_H hd') hd (liftJ J) ?_ ?_ hU' hP' ((strictTop_ofDR hd J _).mpr hs)
  · exact ⟨d + 1, fun j => hom (J (DLetter.mark Letter.lft)) (c0 hd) j, homL J,
      homL J Letter.rgt *ᵥ xs hd, fun n => by rw [encFwd, gV_eq_Vw, Vw_fwd_eq]; rfl⟩
  · exact ⟨0, fun n => le_trans (hAP _ (by decide)) (gV_ge_head hd (liftJ J) _ _)⟩

/-! ## Reversed direction (uses of the dynamic rules) -/

theorem rootPDrevH_cases {σ : Rule} (hσ : σ ∈ rootPDrevH) :
    σ = ffRule.rev ∨ σ = tttRule.rev := by
  simp only [rootPDrevH, List.mem_cons, List.not_mem_nil, or_false] at hσ
  exact hσ

/-- The numbers of uses of the dynamic rules along the family (in the form `HUseC`). -/
theorem hUseC_dyn_H {τ : Rule} (hτ : τ = ffRule ∨ τ = tttRule) :
    HUseC Hmap hR hSteps (fun n => (canDerivH n).count τ) := by
  rcases hτ with rfl | rfl
  · exact (hUseR_iff_use _ _ _ _ _).mp (specDynUseH specHModel specHClass).1
  · exact (hUseR_iff_use _ _ _ _ _).mp (specDynUseH specHModel specHClass).2

/-- Condition (a), reversed: carry over the reversed canonical dependency pair chains at points of family orbits (`σ = τ.rev`). -/
theorem rev_chain_H {τ : Rule} (hσU : τ.rev ∉ usableHTrev) (n : ℕ)
    (hn : famDom (modelOf specHModel) n) :
    ∃ es, GDChain (usableHTrev.map plainR) (rootPDrevH.map (dpR Letter.rgt)) es (encRev n)
      (encRev (Hmap n)) ∧
      (canDerivH n).count τ ≤ es.count (GLabel.root (dpR Letter.rgt τ.rev)) := by
  obtain ⟨es, hch, hle⟩ := gdchain_of_dchain Letter.rgt hσU (dcanDerivH_rev n hn.2)
  refine ⟨es, hch, ?_⟩
  rw [count_revH] at hle
  exact hle

/-- Common part of the reversed direction: write the root pair `σ ∈ rootPDrevH` as `τ.rev` (`τ` a dynamic rule). -/
theorem rev_setup_H {σ : Rule} (hσ : σ ∈ rootPDrevH) :
    ∃ τ, (τ = ffRule ∨ τ = tttRule) ∧ σ = τ.rev ∧ τ.rev ∉ usableHTrev := by
  rcases rootPDrevH_cases hσ with rfl | rfl
  · exact ⟨ffRule, Or.inl rfl, rfl, by decide⟩
  · exact ⟨tttRule, Or.inr rfl, rfl, by decide⟩

/-- **Theorem 3.3 ($\mathcal H$, reversed, `𝔸_ℕ`) from the general lemma (family form)**. -/
theorem arcticBarrierHDPrev_gen : ArcticBarrierHDPrev := by
  intro d hd J hSF hU hP π hπ hs
  rw [pairsPDrevH_eq] at hπ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hπ
  obtain ⟨τ, hτ, rfl, hσU⟩ := rev_setup_H hσ
  obtain ⟨hU', hP'⟩ := weak_lift hd J Letter.rgt pairsPDrevH_eq hU hP
  refine simulation_family_arc (modelOf specHModel) hTerrasWinR_H (hUseC_dyn_H hτ) encRev
    (usableHTrev.map plainR) (rootPDrevH.map (dpR Letter.rgt)) (dpR Letter.rgt τ.rev)
    (rev_chain_H hσU) hd (liftJ J) ?_ ?_ hU' hP' ((strictTop_ofDR hd J _).mpr hs)
  · exact ⟨d + 1, homL J Letter.lft *ᵥ xs hd, fun s => (homL J s)ᵀ,
      fun j => hom (J (DLetter.mark Letter.rgt)) (c0 hd) j,
      fun n => by rw [encRev, gV_eq_Vw, Vw_rev_eq]; rfl⟩
  · intro n
    rw [encRev, gV_eq_Vw]
    exact Vw_ne_zero hd J lettersPDrev hSF Letter.rgt (by decide) _ (rev_letters n)

/-- **Theorem 3.4 ($\mathcal H$, reversed, below zero) from the general lemma (family form)**. -/
theorem arcticBarrierHBZrev_gen : ArcticBarrierHBZrev := by
  intro d hd J hAP hU hP π hπ hs
  rw [pairsPDrevH_eq] at hπ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hπ
  obtain ⟨τ, hτ, rfl, hσU⟩ := rev_setup_H hσ
  obtain ⟨hU', hP'⟩ := weak_lift hd J Letter.rgt pairsPDrevH_eq hU hP
  refine simulation_family_arcZ (modelOf specHModel) hTerrasWinR_H (hUseC_dyn_H hτ) encRev
    (usableHTrev.map plainR) (rootPDrevH.map (dpR Letter.rgt)) (dpR Letter.rgt τ.rev)
    (rev_chain_H hσU) hd (liftJ J) ?_ ?_ hU' hP' ((strictTop_ofDR hd J _).mpr hs)
  · exact ⟨d + 1, homL J Letter.lft *ᵥ xs hd, fun s => (homL J s)ᵀ,
      fun j => hom (J (DLetter.mark Letter.rgt)) (c0 hd) j,
      fun n => by rw [encRev, gV_eq_Vw, Vw_rev_eq]; rfl⟩
  · exact ⟨0, fun n => le_trans (hAP _ (by decide)) (gV_ge_head hd (liftJ J) _ _)⟩

end Collatz.Arctic.DPGen
