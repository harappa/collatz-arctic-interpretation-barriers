/-
Lean foundation of Section 8 (Section 8.1): a check. The frozen dependency pair theorems for $\mathcal T$ are re-derived as instances of the general lemma
(`Sim.lean`). This file is not in the closure of the main theorems for $\mathcal T$ (`Summary.lean`).

* `arcticBarrierDP_gen : ArcticBarrierDP` (Theorem 3.3, forward, `𝔸_ℕ`) and `arcticBarrierBZ_gen : ArcticBarrierBZ`
  (Theorem 3.4, forward, below zero) are derived in the **family form** (`simulation_family_arc(Z)`): (a) only at points of family orbits
  (carrying `DPCanon.dcanDeriv` over by `STConv.gdchain_of_dchain`), and (c) by Corollary 8.1 (`Family.autoUseG_family`)
  from the window frequencies `hTerrasWinR_T` of $T$ and the uses `hLeftUse` of the left-end rules. They do not go through `AutoCore`.
* `arcticBarrierDPrev_gen`, `arcticBarrierBZrev_gen` (reversed): the root pairs are the reversals of the dynamic rules, and the numbers of uses of the dynamic
  rules of $T$ along the family are not in Lean in the form `HUseR`, so these are derived in the **form on the whole domain** (`simulation_arc(Z)`,
  `dom n := 2 ≤ n`), with (c) from the frozen `AutoCore` (`CoreFinal.autoCore_of_hyps`). The value is that of an automaton that reads from the most
  significant digit after transposition (`DPBridge.Vw_rev_eq`).
* The encodings are the canonical strings: forward `encFwd n = lft# bin'(n) rgt`, reversed `encRev n = rgt# rev(bin'(n)) lft`.
-/
import CollatzProof.Arctic.DPGen.Sim
import CollatzProof.Arctic.DPGen.STConv
import CollatzProof.Arctic.DPGen.FamilyInst
import CollatzProof.Arctic.DPMain
import CollatzProof.Arctic.BZMain
import CollatzProof.Arctic.CoreFinal

namespace Collatz.Arctic.DPGen

open Collatz.Arctic Collatz.Arctic.Gen Matrix

/-- The forward encoding (the canonical string `lft# bin'(n) rgt`). -/
def encFwd (n : ℕ) : List (GLetter Letter) :=
  GLetter.mark Letter.lft :: (binTail n ++ [Letter.rgt]).map GLetter.plain

/-- The reversed encoding (`rgt# rev(bin'(n)) lft`). -/
def encRev (n : ℕ) : List (GLetter Letter) :=
  GLetter.mark Letter.rgt :: ((binTail n).reverse ++ [Letter.lft]).map GLetter.plain

theorem rootPB_cases {σ : Rule} (hσ : σ ∈ rootPB) : ∃ d, d ≤ 2 ∧ σ = leftRule d := by
  simp only [rootPB, List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl
  exacts [⟨0, by norm_num, rfl⟩, ⟨1, by norm_num, rfl⟩, ⟨2, by norm_num, rfl⟩]

theorem fwd_letters (n : ℕ) : ∀ s ∈ binTail n ++ [Letter.rgt], DLetter.plain s ∈ lettersPB := by
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · rcases binTail_letters n s hs with rfl | rfl <;> decide
  · rw [List.mem_singleton] at hs; subst hs; decide

theorem rev_letters (n : ℕ) :
    ∀ s ∈ (binTail n).reverse ++ [Letter.lft], DLetter.plain s ∈ lettersPDrev := by
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · rcases binTail_letters n s (List.mem_reverse.mp hs) with rfl | rfl <;> decide
  · rw [List.mem_singleton] at hs; subst hs; decide

/-- Carrying over the constraints on `U` and `P` (over either semiring). -/
theorem weak_lift {R : Type} [CommSemiring R] [LE R] {d : ℕ} (hd : 0 < d) (J : DLetter → AffFun R d)
    {U : List Rule} {PR : List Rule} (h : Letter) {PD : List DRule} (hPD : PD = PR.map (dp h))
    (hU : ∀ ρ ∈ U, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs))
    (hP : ∀ π ∈ PD, WeakTop hd (evA J π.lhs) (evA J π.rhs)) :
    (∀ ρ ∈ U.map plainR, WeakA (gevA (liftJ J) ρ.lhs) (gevA (liftJ J) ρ.rhs)) ∧
      ∀ π ∈ PR.map (dpR h), WeakTop hd (gevA (liftJ J) π.lhs) (gevA (liftJ J) π.rhs) := by
  refine ⟨fun ρ' hρ' => ?_, fun π' hπ' => ?_⟩
  · obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hρ'
    exact (weakA_ofDR J ρ.plain).mpr (hU ρ hρ)
  · obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hπ'
    exact (weakTop_ofDR hd J (dp h ρ)).mpr (hP _ (by rw [hPD]; exact List.mem_map_of_mem hρ))

/-! ## Forward direction (family form) -/

/-- **Theorem 3.3 ($\mathcal T$, forward, `𝔸_ℕ`) from the general lemma (family form)**. -/
theorem arcticBarrierDP_gen : ArcticBarrierDP := by
  intro d hd J hSF hU hP π hπ hs
  rw [pairsPB_eq] at hπ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hπ
  obtain ⟨d', hd', rfl⟩ := rootPB_cases hσ
  have hσU : leftRule d' ∉ usableST := by interval_cases d' <;> decide
  have hUse : HUseC tModel.f tModel.R tModel.steps (fun n => (canDeriv n).count (leftRule d')) :=
    (hUseR_iff_use _ _ _ _ _).mp (hUseR_of_hLeftUse hLeftUse d' hd')
  obtain ⟨hU', hP'⟩ := weak_lift hd J Letter.lft pairsPB_eq hU hP
  refine simulation_family_arc tModel hTerrasWinR_T hUse encFwd (usableST.map plainR)
    (rootPB.map (dpR Letter.lft)) (dpR Letter.lft (leftRule d')) ?_ hd (liftJ J) ?_ ?_ hU' hP'
    ((strictTop_ofDR hd J _).mpr hs)
  · intro n hn
    exact gdchain_of_dchain Letter.lft hσU (dcanDeriv n hn.2)
  · exact ⟨d + 1, fun j => hom (J (DLetter.mark Letter.lft)) (c0 hd) j, homL J,
      homL J Letter.rgt *ᵥ xs hd, fun n => by rw [encFwd, gV_eq_Vw, Vw_fwd_eq]; rfl⟩
  · intro n
    rw [encFwd, gV_eq_Vw]
    exact Vw_ne_zero hd J lettersPB hSF Letter.lft (by decide) _ (fwd_letters n)

/-- **Theorem 3.4 ($\mathcal T$, forward, below zero) from the general lemma (family form)**. -/
theorem arcticBarrierBZ_gen : ArcticBarrierBZ := by
  intro d hd J hAP hU hP π hπ hs
  rw [pairsPB_eq] at hπ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hπ
  obtain ⟨d', hd', rfl⟩ := rootPB_cases hσ
  have hσU : leftRule d' ∉ usableST := by interval_cases d' <;> decide
  have hUse : HUseC tModel.f tModel.R tModel.steps (fun n => (canDeriv n).count (leftRule d')) :=
    (hUseR_iff_use _ _ _ _ _).mp (hUseR_of_hLeftUse hLeftUse d' hd')
  obtain ⟨hU', hP'⟩ := weak_lift hd J Letter.lft pairsPB_eq hU hP
  refine simulation_family_arcZ tModel hTerrasWinR_T hUse encFwd (usableST.map plainR)
    (rootPB.map (dpR Letter.lft)) (dpR Letter.lft (leftRule d')) ?_ hd (liftJ J) ?_ ?_ hU' hP'
    ((strictTop_ofDR hd J _).mpr hs)
  · intro n hn
    exact gdchain_of_dchain Letter.lft hσU (dcanDeriv n hn.2)
  · exact ⟨d + 1, fun j => hom (J (DLetter.mark Letter.lft)) (c0 hd) j, homL J,
      homL J Letter.rgt *ᵥ xs hd, fun n => by rw [encFwd, gV_eq_Vw, Vw_fwd_eq]; rfl⟩
  · exact ⟨0, fun n => le_trans (hAP _ (by decide)) (gV_ge_head hd (liftJ J) _ _)⟩

/-! ## Reversed direction (form on the whole domain, from `AutoCore`) -/

/-- The frozen `AutoCore` (without hypotheses; the same assembly as in `Summary.lean`). -/
theorem autoCore_holds : AutoCore :=
  autoCore_of_hyps hsp_holds (hTerrasWin_of_key hKeyTop) hLeftUse

/-- From `AutoCore`, `AutoUseG` for the count of a rule `τ ∈ rulesST` (domain `2 ≤ n`). -/
theorem autoUse_of_core {τ : Rule} (hτ : τ ∈ rulesST) :
    AutoUseG T (fun n => 2 ≤ n) (fun n => (canDeriv n).count τ) :=
  fun D u A c κ hfin hsl N => autoCore_holds D u A c κ hfin hsl τ hτ N

/-- Carrying over the reversed chains (`σ = τ.rev`): the original number of uses `(canDeriv n).count τ` is at most the number of root uses. -/
theorem rev_chain {τ : Rule} (hσU : τ.rev ∉ usableSTrev) (n : ℕ) (hn : 2 ≤ n) :
    ∃ es, GDChain (usableSTrev.map plainR) (rootPDrev.map (dpR Letter.rgt)) es (encRev n)
      (encRev (T n)) ∧ (canDeriv n).count τ ≤ es.count (GLabel.root (dpR Letter.rgt τ.rev)) := by
  obtain ⟨es, hch, hle⟩ := gdchain_of_dchain Letter.rgt hσU (dcanDeriv_rev n hn)
  refine ⟨es, hch, ?_⟩
  rw [count_rev] at hle
  exact hle

/-- **Theorem 3.3 ($\mathcal T$, reversed, `𝔸_ℕ`) from the general lemma**. -/
theorem arcticBarrierDPrev_gen : ArcticBarrierDPrev := by
  intro d hd J hSF hU hP π hπ hs
  rw [pairsPDrev_eq] at hπ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hπ
  have hσU : σ ∉ usableSTrev := by
    simp only [rootPDrev, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl <;> decide
  obtain ⟨τ, hτ, rfl⟩ := rootPDrev_mem hσ
  obtain ⟨hU', hP'⟩ := weak_lift hd J Letter.rgt pairsPDrev_eq hU hP
  refine simulation_arc encRev (usableSTrev.map plainR) (rootPDrev.map (dpR Letter.rgt))
    (dpR Letter.rgt τ.rev) (fun n hn => rev_chain hσU n hn) (autoUse_of_core hτ) hd (liftJ J)
    ?_ ?_ hU' hP' ((strictTop_ofDR hd J _).mpr hs)
  · exact ⟨d + 1, homL J Letter.lft *ᵥ xs hd, fun s => (homL J s)ᵀ,
      fun j => hom (J (DLetter.mark Letter.rgt)) (c0 hd) j,
      fun n => by rw [encRev, gV_eq_Vw, Vw_rev_eq]; rfl⟩
  · intro n
    rw [encRev, gV_eq_Vw]
    exact Vw_ne_zero hd J lettersPDrev hSF Letter.rgt (by decide) _ (rev_letters n)

/-- **Theorem 3.4 ($\mathcal T$, reversed, below zero) from the general lemma**. -/
theorem arcticBarrierBZrev_gen : ArcticBarrierBZrev := by
  intro d hd J hAP hU hP π hπ hs
  rw [pairsPDrev_eq] at hπ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hπ
  have hσU : σ ∉ usableSTrev := by
    simp only [rootPDrev, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl <;> decide
  obtain ⟨τ, hτ, rfl⟩ := rootPDrev_mem hσ
  obtain ⟨hU', hP'⟩ := weak_lift hd J Letter.rgt pairsPDrev_eq hU hP
  refine simulation_arcZ encRev (usableSTrev.map plainR) (rootPDrev.map (dpR Letter.rgt))
    (dpR Letter.rgt τ.rev) (fun n hn => rev_chain hσU n hn) (autoUse_of_core hτ) hd (liftJ J)
    ?_ ?_ hU' hP' ((strictTop_ofDR hd J _).mpr hs)
  · exact ⟨d + 1, homL J Letter.lft *ᵥ xs hd, fun s => (homL J s)ᵀ,
      fun j => hom (J (DLetter.mark Letter.rgt)) (c0 hd) j,
      fun n => by rw [encRev, gV_eq_Vw, Vw_rev_eq]; rfl⟩
  · exact ⟨0, fun n => le_trans (hAP _ (by decide)) (gV_ge_head hd (liftJ J) _ _)⟩

end Collatz.Arctic.DPGen
