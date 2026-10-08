/-
The below-zero forms with argument filters under the weaker hypothesis `BZPos` (the remark on argument filters after Theorem 3.4 of the paper; internal independent review).
The statements are `ArcticBarrierBZFiltW`, `BZrevFiltW`, `HBZFiltW`, `HBZrevFiltW` of `DPFilterStatement.lean`.

* Finding of the internal review: Theorem 26 of Giesl–Thiemann–Schneider-Kamp–Falke 2006 allows collapsing filters (`π(s) = 1`). Written with the original symbols, a collapsed symbol is the identity, which below zero
  is not absolutely positive. Hence the statements that require absolute positivity of all symbols (`ArcticBarrierBZFilt` etc., and the frozen
  `ArcticBarrierBZ` etc.) do not include the interpretations of that case.
* Here the hypothesis is weakened to `BZPos` (the marked symbol `h#` is absolutely positive, or all symbols of the problem satisfy `FirstNonneg`: `M_s[1,1] ≥ 0` or
  `c_s[1] ≥ 0`). The proof uses only that the value `V(w) = ([h# w](x*))₁` is non-negative (`Vw_nonneg`) and, in the case of `f`,
  that `c_{h#}[1]` is finite (`markC_ne_zero_of_row0`). An interpretation of the filtered signature that is absolutely positive gives, read on the original
  symbols, `FirstNonneg` for every symbol (`c_s[1] ≥ 0` for a symbol whose argument is dropped, and a collapsed symbol is the identity, with `M_s[1,1] = 0`; `firstNonneg_of_ap_or_id`).
  Also if `.#` (`/#`) itself is collapsed, the value is non-negative by `FirstNonneg`.
* The usable rules do not shrink: for $\mathcal T$, the core lemmas `dw_BZ_core`, `dw_BZrev_core` of `DPWeak2.lean` (with lower bound `C = 0`). For $\mathcal H$,
  the proofs of `barrierHBZ_of_auto`, `barrierHBZrev_of_auto` of `HTPDB/Main.lean` are copied, with the values shown to be natural numbers by `BZPos`
  (`AutoCoreH` is obtained from the same component proofs as in `HTPDB/Final.lean`).
* The usable rules shrink: the argument of §3 of `DPFilter.lean` (`rev_t_value`, `revH_ft_value`, `row0_zero_of_weakTop`).
* The frozen statements and `ArcticBarrierBZFilt` etc. are corollaries of this form (`BZFilt_of_W` etc.).
-/
import CollatzProof.Arctic.DPFilter
import CollatzProof.Arctic.DPWeak2

namespace Collatz.Arctic.DPFilter

open Collatz.Arctic Matrix Letter DLetter
open Collatz.Arctic.NatQ5.W5 (usableRevT usableFilt_rev usableFilt_fwd pairsPDrev_head pairsPB_head)

variable {d : ℕ}

/-! ## §1 The values are non-negative -/

theorem firstNonneg_of_absPositive (hd : 0 < d) (J : DLetter → AffFun ArcZ d) (S : List DLetter)
    (h : AbsPositive hd J S) : FirstNonneg hd J S :=
  fun s hs => Or.inr (h s hs)

/-- If every symbol of the problem is absolutely positive or the identity (a collapsed symbol), then `FirstNonneg` holds. -/
theorem firstNonneg_of_ap_or_id (hd : 0 < d) (J : DLetter → AffFun ArcZ d) (S : List DLetter)
    (h : ∀ s ∈ S, ArcZ.fin 0 ≤ (J s).c ⟨0, hd⟩ ∨ J s = AffFun.id) : FirstNonneg hd J S := by
  intro s hs
  rcases h s hs with hc | hid
  · exact Or.inr hc
  · left
    rw [hid]
    show ArcZ.fin 0 ≤ (1 : Matrix (Fin d) (Fin d) ArcZ) ⟨0, hd⟩ ⟨0, hd⟩
    rw [Matrix.one_apply_eq]
    exact le_rfl

theorem bzPos_of_absPositive (hd : 0 < d) (J : DLetter → AffFun ArcZ d) (h : Letter) (S : List DLetter)
    (hh : mark h ∈ S) (hAP : AbsPositive hd J S) : BZPos hd J h S :=
  Or.inl (fun s hs => hAP s (by rw [List.mem_singleton] at hs; subst hs; exact hh))

theorem arcZ_fin0_mul {a b : ArcZ} (ha : ArcZ.fin 0 ≤ a) (hb : ArcZ.fin 0 ≤ b) : ArcZ.fin 0 ≤ a * b := by
  have := ArcticOrder.mul_mono ha hb
  rwa [ArcZ.fin_mul_fin, add_zero] at this

/-- For a string of symbols that satisfy `FirstNonneg`, the first component of the value vector is non-negative. -/
theorem yvec_nonneg (hd : 0 < d) (J : DLetter → AffFun ArcZ d) (S : List DLetter) (hS : FirstNonneg hd J S) :
    ∀ w : Word, (∀ s ∈ w, plain s ∈ S) → ArcZ.fin 0 ≤ (evR (homL J) w *ᵥ xs hd) (c0 hd) := by
  intro w
  induction w with
  | nil =>
    intro _
    simp only [evR_nil, Matrix.one_mulVec, xs, c0, Fin.lastCases_castSucc, ↓reduceIte]
    exact le_rfl
  | cons s w ih =>
    intro hw
    have hrest := ih (fun s' hs' => hw s' (List.mem_cons_of_mem _ hs'))
    rw [evR_cons, ← Matrix.mulVec_mulVec]
    rcases hS _ (hw s List.mem_cons_self) with hM | hc
    · exact (arcZ_fin0_mul hM hrest).trans (hom_mulVec_ge_M hd (J (plain s)) _)
    · refine le_trans ?_ (hom_mulVec_ge_c hd (J (plain s)) _)
      rw [yvec_last, mul_one]
      exact hc

/-- **Under `BZPos` the value `V(w)` is non-negative** (the symbols of `w` are symbols of the problem). -/
theorem Vw_nonneg (hd : 0 < d) (J : DLetter → AffFun ArcZ d) (h : Letter) (S : List DLetter) (hh : mark h ∈ S)
    (hB : BZPos hd J h S) (w : Word) (hw : ∀ s ∈ w, plain s ∈ S) : ArcZ.fin 0 ≤ Vw hd J h w := by
  rw [Vw_eq_mulVec]
  rcases hB with hAP | hS
  · refine le_trans ?_ (hom_mulVec_ge_c hd _ _)
    rw [yvec_last, mul_one]
    exact hAP _ List.mem_cons_self
  · rcases hS _ hh with hM | hc
    · exact (arcZ_fin0_mul hM (yvec_nonneg hd J S hS w hw)).trans (hom_mulVec_ge_M hd _ _)
    · refine le_trans ?_ (hom_mulVec_ge_c hd _ _)
      rw [yvec_last, mul_one]
      exact hc

/-- If the first row of the matrix of `h#` is −∞, then `c_{h#}[1]` is finite (non-negative) by `BZPos`. -/
theorem markC_ne_zero_of_row0 (hd : 0 < d) (J : DLetter → AffFun ArcZ d) (h : Letter) (S : List DLetter)
    (hh : mark h ∈ S) (hB : BZPos hd J h S) (hrow : ∀ j, (J (mark h)).M ⟨0, hd⟩ j = 0) :
    (J (mark h)).c ⟨0, hd⟩ ≠ 0 := by
  rcases hB with hAP | hS
  · exact arcZ_ne_zero_of_pos (hAP _ List.mem_cons_self)
  · rcases hS _ hh with hM | hc
    · exfalso
      rw [hrow, ArcZ.le_iff_val] at hM
      simp at hM
    · exact arcZ_ne_zero_of_pos hc

theorem fwd_letters' (n : ℕ) : ∀ s ∈ binTail n ++ [rgt], plain s ∈ lettersPB := by
  intro s hs
  rcases dw_fwd_letters n s hs with rfl | rfl | rfl <;> decide

theorem rev_letters' (n : ℕ) : ∀ s ∈ (binTail n).reverse ++ [lft], plain s ∈ lettersPDrev := by
  intro s hs
  rcases dw_rev_letters n s hs with rfl | rfl | rfl <;> decide

/-! ## §2 The usable rules do not shrink -/

/-- $\mathcal T$, forward, below zero, `BZPos` (the frozen usable rules). -/
theorem bz_fwd_bzpos (hd : 0 < d) (J : DLetter → AffFun ArcZ d) (hB : BZPos hd J lft lettersPB)
    (hU : ∀ ρ ∈ usableST, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs))
    (hP : ∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) :
    ∀ π ∈ pairsPB, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs) :=
  dw_BZ_core dw_autoCore hd J hU hP ⟨0, fun n => Vw_nonneg hd J lft lettersPB (by decide) hB _ (fwd_letters' n)⟩

/-- $\mathcal T$, reversed, below zero, `BZPos`. -/
theorem bz_rev_bzpos (hd : 0 < d) (J : DLetter → AffFun ArcZ d) (hB : BZPos hd J rgt lettersPDrev)
    (hU : ∀ ρ ∈ usableSTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs))
    (hP : ∀ π ∈ pairsPDrev, WeakTop hd (evA J π.lhs) (evA J π.rhs)) :
    ∀ π ∈ pairsPDrev, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs) :=
  dw_BZrev_core dw_autoCore hd J hU hP
    ⟨0, fun n => Vw_nonneg hd J rgt lettersPDrev (by decide) hB _ (rev_letters' n)⟩

/-- `AutoCoreH` of $\mathcal H$ (from the same component proofs as `htpdbBarriers` in `HTPDB/Final.lean`). -/
theorem autoCoreH_dpf : HTPDB.AutoCoreH :=
  HTPDB.autoCoreH_of_specs hsp_holds HModel.specHModel HModel.specHClass HModel.specHBoundary HModel.specHSwap
    Gen.specAutoRule Gen.specKeyOfSwap Gen.specWinOfKey Gen.specQuadRule HTPDB.specLeftUseH HTPDB.specDynUseH
    HTPDB.specQuadH

/-- $\mathcal H$, forward, below zero, `BZPos` (a copy of the proof of `HTPDB.barrierHBZ_of_auto`). -/
theorem hbz_fwd_bzpos (hd : 0 < d) (J : DLetter → AffFun ArcZ d) (hB : BZPos hd J lft lettersPB)
    (hU : ∀ ρ ∈ HTPDB.usableHT, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs))
    (hP : ∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) :
    ∀ π ∈ pairsPB, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs) := by
  intro π hπ hs
  rw [pairsPB_eq] at hπ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hπ
  have hPw : ∀ ρ ∈ rootPB, WeakTop hd (evA J (dp lft ρ).lhs) (evA J (dp lft ρ).rhs) :=
    fun ρ hρ => hP _ (by rw [pairsPB_eq]; exact List.mem_map_of_mem hρ)
  have hσ' : σ ∉ HTPDB.usableHT ∧ σ ∈ HTPDB.rulesHT := by
    simp only [rootPB, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl | rfl <;> decide
  refine Gen.barrier_of_auto_arcZG autoCoreH_dpf (fun j => hom (J (mark lft)) (c0 hd) j)
    (homL J) (homL J rgt *ᵥ xs hd) σ hσ'.2 ?_ ?_
  · intro n
    obtain ⟨z, hz⟩ := ArcZ.exists_nat_of_le (Vw_nonneg hd J lft lettersPB (by decide) hB _ (fwd_letters' n))
    exact ⟨z, by rw [autoValZ, ← Vw_fwd_eq]; exact hz⟩
  · intro n hn
    have := Vw_chain hd J lft (ArcZ.fin 1) (fun _ _ h => ArcZ.gg_mul_fin_one h) hU hPw hσ'.1 hs
      (HTPDB.dcanDerivH n hn)
    rwa [Vw_fwd_eq, Vw_fwd_eq] at this

/-- $\mathcal H$, reversed, below zero, `BZPos` (a copy of the proof of `HTPDB.barrierHBZrev_of_auto`). -/
theorem hbz_rev_bzpos (hd : 0 < d) (J : DLetter → AffFun ArcZ d) (hB : BZPos hd J rgt lettersPDrev)
    (hU : ∀ ρ ∈ HTPDB.usableHTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs))
    (hP : ∀ π ∈ HTPDB.pairsPDrevH, WeakTop hd (evA J π.lhs) (evA J π.rhs)) :
    ∀ π ∈ HTPDB.pairsPDrevH, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs) := by
  intro π hπ hs
  rw [HTPDB.pairsPDrevH_eq] at hπ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hπ
  have hPw : ∀ ρ ∈ HTPDB.rootPDrevH, WeakTop hd (evA J (dp rgt ρ).lhs) (evA J (dp rgt ρ).rhs) :=
    fun ρ hρ => hP _ (by rw [HTPDB.pairsPDrevH_eq]; exact List.mem_map_of_mem hρ)
  have hσU : σ ∉ HTPDB.usableHTrev := by
    simp only [HTPDB.rootPDrevH, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl <;> decide
  obtain ⟨τ, hτ, rfl⟩ := HTPDB.rootPDrevH_mem hσ
  refine Gen.barrier_of_auto_arcZG autoCoreH_dpf (homL J lft *ᵥ xs hd) (fun s => (homL J s)ᵀ)
    (fun j => hom (J (mark rgt)) (c0 hd) j) τ hτ ?_ ?_
  · intro n
    obtain ⟨z, hz⟩ :=
      ArcZ.exists_nat_of_le (Vw_nonneg hd J rgt lettersPDrev (by decide) hB _ (rev_letters' n))
    exact ⟨z, by rw [autoValZ, ← Vw_rev_eq]; exact hz⟩
  · intro n hn
    have := Vw_chain hd J rgt (ArcZ.fin 1) (fun _ _ h => ArcZ.gg_mul_fin_one h) hU hPw hσU hs
      (HTPDB.dcanDerivH_rev n hn)
    rwa [Vw_rev_eq, Vw_rev_eq, HTPDB.count_revH] at this

/-! ## §3 The usable rules shrink -/

/-- **$\mathcal T^{\mathrm{rev}}$, the argument of `f` dropped (below zero, `BZPos`)**. -/
theorem dprev_filt_f_bz (hd : 0 < d) (J : DLetter → AffFun ArcZ d) (hB : BZPos hd J rgt lettersPDrev)
    (hf : (J (plain f)).M = 0) (hP0 : WeakTop hd (evA J [mark rgt, plain f]) (evA J [mark rgt])) :
    ∀ π ∈ pairsPDrev, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs) := by
  have hrow := row0_zero_of_weakTop hd J rgt f hf hP0
  have hc := markC_ne_zero_of_row0 hd J rgt lettersPDrev (by decide) hB hrow
  intro π hπ
  obtain ⟨l, r, hl, hr⟩ := pairsPDrev_head π hπ
  rw [hl, hr]
  exact not_strictTop_of_row0 hd J rgt hrow hc l r

/-- **$\mathcal T^{\mathrm{rev}}$, the argument of `t` dropped (below zero, `BZPos`)**. -/
theorem dprev_filt_t_bz (hd : 0 < d) (J : DLetter → AffFun ArcZ d) (hB : BZPos hd J rgt lettersPDrev)
    (ht : (J (plain t)).M = 0) (hU : ∀ ρ ∈ usableRevT, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs))
    (hP : ∀ π ∈ pairsPDrev, WeakTop hd (evA J π.lhs) (evA J π.rhs)) :
    ∀ π ∈ pairsPDrev, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs) := fun _ hπ hs =>
  arcZ_not_succ_le
    (arcZ_ne_zero_of_pos (Vw_nonneg hd J rgt lettersPDrev (by decide) hB [t, f, f, lft] (by decide)))
    (rev_t_value hd J (ArcZ.fin 1) (fun _ _ h => ArcZ.gg_mul_fin_one h) ht hU hP hπ hs)

/-- **$\mathcal H^{\mathrm{rev}}$, the arguments of `f` and `t` dropped (below zero, `BZPos`)**. -/
theorem dprevH_filt_ft_bz (hd : 0 < d) (J : DLetter → AffFun ArcZ d) (hB : BZPos hd J rgt lettersPDrev)
    (hf : (J (plain f)).M = 0) (ht : (J (plain t)).M = 0)
    (hU : ∀ ρ ∈ usableRevHFT, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs))
    (hP : ∀ π ∈ HTPDB.pairsPDrevH, WeakTop hd (evA J π.lhs) (evA J π.rhs)) :
    ∀ π ∈ HTPDB.pairsPDrevH, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs) := by
  intro π hπ hs
  rcases revH_ft_value hd J (ArcZ.fin 1) (fun _ _ h => ArcZ.gg_mul_fin_one h) hf ht hU hP hπ hs with h1 | h2
  · exact arcZ_not_succ_le
      (arcZ_ne_zero_of_pos (Vw_nonneg hd J rgt lettersPDrev (by decide) hB [f, f, f, lft] (by decide))) h1
  · exact arcZ_not_succ_le
      (arcZ_ne_zero_of_pos (Vw_nonneg hd J rgt lettersPDrev (by decide) hB [t, t, t, t, lft] (by decide))) h2

/-- The argument of the marked symbol dropped (below zero, `BZPos`): in the three problems no dependency pair is strictly oriented in the first row. -/
theorem markConst_not_strict_bzpos (hd : 0 < d) (J : DLetter → AffFun ArcZ d) :
    (BZPos hd J lft lettersPB → (J (mark lft)).M = 0 →
      ∀ π ∈ pairsPB, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)) ∧
    (BZPos hd J rgt lettersPDrev → (J (mark rgt)).M = 0 →
      ∀ π ∈ pairsPDrev, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)) ∧
    (BZPos hd J rgt lettersPDrev → (J (mark rgt)).M = 0 →
      ∀ π ∈ HTPDB.pairsPDrevH, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)) := by
  have key : ∀ (h : Letter) (S : List DLetter), mark h ∈ S → BZPos hd J h S → (J (mark h)).M = 0 →
      (J (mark h)).c ⟨0, hd⟩ ≠ 0 := fun h S hh hB hM =>
    markC_ne_zero_of_row0 hd J h S hh hB (fun j => by simp [hM])
  refine ⟨fun hB hM => ?_, fun hB hM => ?_, fun hB hM => ?_⟩
  · exact markConst_not_strict hd J lft hM (key _ _ (by decide) hB hM) _ pairsPB_head
  · exact markConst_not_strict hd J rgt hM (key _ _ (by decide) hB hM) _ pairsPDrev_head
  · exact markConst_not_strict hd J rgt hM (key _ _ (by decide) hB hM) _ pairsPDrevH_head

/-! ## §4 The main theorems (without hypotheses), and the implications for the forms with absolute positivity -/

/-- **Theorem 3.4 with an argument filter ($\mathcal T$, forward, below zero, `BZPos`)**. -/
theorem arcticBarrierBZFiltW : ArcticBarrierBZFiltW := by
  intro F d hd J hB _ hU hP
  rw [usableFilt_fwd] at hU
  exact bz_fwd_bzpos hd J hB hU hP

/-- **Theorem 3.4 with an argument filter ($\mathcal T$, reversed, below zero, `BZPos`)**. -/
theorem arcticBarrierBZrevFiltW : ArcticBarrierBZrevFiltW := by
  intro F d hd J hB hF hU hP
  rw [usableFilt_rev] at hU
  by_cases hf : f ∈ F
  · exact dprev_filt_f_bz hd J hB (hF f hf) (hP ⟨[mark rgt, plain f], [mark rgt]⟩ (by decide))
  · by_cases ht : t ∈ F
    · simp only [hf, ht, ↓reduceIte] at hU
      exact dprev_filt_t_bz hd J hB (hF t ht) hU hP
    · simp only [hf, ht, ↓reduceIte] at hU
      exact bz_rev_bzpos hd J hB hU hP

/-- **Theorem 3.4 with an argument filter ($\mathcal H$, forward, below zero, `BZPos`)**. -/
theorem arcticBarrierHBZFiltW : ArcticBarrierHBZFiltW := by
  intro F d hd J hB _ hU hP
  rw [usableFiltH_fwd] at hU
  exact hbz_fwd_bzpos hd J hB hU hP

/-- **Theorem 3.4 with an argument filter ($\mathcal H$, reversed, below zero, `BZPos`)**. -/
theorem arcticBarrierHBZrevFiltW : ArcticBarrierHBZrevFiltW := by
  intro F d hd J hB hF hU hP
  rw [usableFiltH_rev] at hU
  by_cases hft : f ∈ F ∧ t ∈ F
  · simp only [hft.1, hft.2, and_self, ↓reduceIte] at hU
    exact dprevH_filt_ft_bz hd J hB (hF f hft.1) (hF t hft.2) hU hP
  · simp only [hft, ↓reduceIte] at hU
    exact hbz_rev_bzpos hd J hB hU hP

theorem BZFilt_of_W (h : ArcticBarrierBZFiltW) : ArcticBarrierBZFilt := fun F d hd J hAP =>
  h F d hd J (bzPos_of_absPositive hd J lft lettersPB (by decide) hAP)

theorem BZrevFilt_of_W (h : ArcticBarrierBZrevFiltW) : ArcticBarrierBZrevFilt := fun F d hd J hAP =>
  h F d hd J (bzPos_of_absPositive hd J rgt lettersPDrev (by decide) hAP)

theorem HBZFilt_of_W (h : ArcticBarrierHBZFiltW) : ArcticBarrierHBZFilt := fun F d hd J hAP =>
  h F d hd J (bzPos_of_absPositive hd J lft lettersPB (by decide) hAP)

theorem HBZrevFilt_of_W (h : ArcticBarrierHBZrevFiltW) : ArcticBarrierHBZrevFilt := fun F d hd J hAP =>
  h F d hd J (bzPos_of_absPositive hd J rgt lettersPDrev (by decide) hAP)

/-- The four below-zero forms with filters under the weaker hypothesis (without hypotheses). -/
theorem arcticBarrierBZFiltW_all :
    ArcticBarrierBZFiltW ∧ ArcticBarrierBZrevFiltW ∧ ArcticBarrierHBZFiltW ∧ ArcticBarrierHBZrevFiltW :=
  ⟨arcticBarrierBZFiltW, arcticBarrierBZrevFiltW, arcticBarrierHBZFiltW, arcticBarrierHBZrevFiltW⟩

end Collatz.Arctic.DPFilter
